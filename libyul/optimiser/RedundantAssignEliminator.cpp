/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/**
 * Optimiser component that removes assignments to variables that are not used
 * until they go out of scope or are re-assigned.
 */

#include <libyul/optimiser/RedundantAssignEliminator.h>

#include <libyul/optimiser/Semantics.h>

#include <libsolidity/inlineasm/AsmData.h>

#include <libdevcore/CommonData.h>

#include <boost/range/algorithm_ext/erase.hpp>

using namespace std;
using namespace dev;
using namespace dev::yul;
using namespace dev::solidity;

void RedundantAssignEliminator::operator()(Identifier const& _identifier)
{
	changeUndecidedTo(_identifier.name, State::Used);
}

void RedundantAssignEliminator::operator()(VariableDeclaration const& _variableDeclaration)
{
	ASTWalker::operator()(_variableDeclaration);

	for (auto const& var: _variableDeclaration.variables)
		m_declaredVariables.insert(var.name);
}

void RedundantAssignEliminator::operator()(Assignment const& _assignment)
{
	visit(*_assignment.value);
	for (auto const& var: _assignment.variableNames)
		changeUndecidedTo(var.name, State::Unused);

	if (_assignment.variableNames.size() == 1)
		// Default-construct it in "Undecided" state if it does not yet exist.
		m_assignments[_assignment.variableNames.front().name][&_assignment];
}

void RedundantAssignEliminator::operator()(If const& _if)
{
	visit(*_if.condition);

	RedundantAssignEliminator branch{*this};
	branch(_if.body);

	join(branch);
}

void RedundantAssignEliminator::operator()(Switch const& _switch)
{
	visit(*_switch.expression);

	bool hasDefault = false;
	vector<RedundantAssignEliminator> branches;
	for (auto const& c: _switch.cases)
	{
		if (!c.value)
			hasDefault = true;
		branches.emplace_back(*this);
		branches.back()(c.body);
	}

	if (hasDefault)
	{
		*this = std::move(branches.back());
		branches.pop_back();
	}
	for (auto& branch: branches)
		join(branch);
}

void RedundantAssignEliminator::operator()(FunctionDefinition const& _functionDefinition)
{
	(*this)(_functionDefinition.body);

	for (auto const& param: _functionDefinition.parameters)
		changeUndecidedTo(param.name, State::Unused);
	for (auto const& retParam: _functionDefinition.returnVariables)
		changeUndecidedTo(retParam.name, State::Used);
}

void RedundantAssignEliminator::operator()(ForLoop const& _forLoop)
{
	// This will set all variables that are declared in this
	// block to "unused" when it is destroyed.
	BlockScope scope(*this);

	// We need to visit the statements directly because of the
	// scoping rules.
	walkVector(_forLoop.pre.statements);

	// We just run the loop twice to account for the
	// back edge.
	// There need not be more runs because we only have three different states.

	visit(*_forLoop.condition);

	RedundantAssignEliminator zeroRuns{*this};

	(*this)(_forLoop.body);
	(*this)(_forLoop.post);

	visit(*_forLoop.condition);

	RedundantAssignEliminator oneRun{*this};

	(*this)(_forLoop.body);
	(*this)(_forLoop.post);

	visit(*_forLoop.condition);

	// Order does not matter because "max" is commutative and associative.
	join(oneRun);
	join(zeroRuns);
}

void RedundantAssignEliminator::operator()(Block const& _block)
{
	// This will set all variables that are declared in this
	// block to "unused" when it is destroyed.
	BlockScope scope(*this);

	ASTWalker::operator()(_block);
}

void RedundantAssignEliminator::run(Block& _ast)
{
	RedundantAssignEliminator rae;
	rae(_ast);

	std::set<Assignment const*> assignmentsToRemove;
	for (auto const& variables: rae.m_assignments)
		for (auto const& assignment: variables.second)
		{
			assertThrow(assignment.second != State::Undecided, OptimizerException, "");
			if (assignment.second == State::Unused && MovableChecker{*assignment.first->value}.movable())
				assignmentsToRemove.insert(assignment.first);
		}

	AssignmentRemover remover{assignmentsToRemove};
	remover(_ast);
}

template <class K, class V, class F>
std::map<K, V> joinMap(std::map<K, V>&& _a, std::map<K, V>&& _b, F _conflictSolver)
{
	// TODO This is still not ideal. Perhaps we should modify in-place?
	std::map<K, V> out;

	auto ita = _a.begin();
	auto aend = _a.end();
	auto itb = _b.begin();
	auto bend = _b.end();

	while (ita != aend || itb != bend)
	{
		if (itb == bend)
			out.emplace_hint(out.end(), std::move(*ita++));
		else if (ita == aend)
			out.emplace_hint(out.end(), std::move(*itb++));
		else if (ita->first < itb->first)
			out.emplace_hint(out.end(), std::move(*ita++));
		else if (itb->first < ita->first)
			out.emplace_hint(out.end(), std::move(*itb++));
		else
		{
			out.emplace_hint(out.end(), std::move(ita->first), _conflictSolver(
				std::move(ita->second),
				std::move(itb->second)
			));
			++ita;
			++itb;
		}
	}

	return out;
}

void RedundantAssignEliminator::join(RedundantAssignEliminator& _other)
{
	std::map<string, std::map<Assignment const*, State>> newAssignments;
	newAssignments = joinMap(std::move(m_assignments), std::move(_other.m_assignments), [](
		map<Assignment const*, State>&& _assignmentHere,
		map<Assignment const*, State>&& _assignmentThere
	) -> map<Assignment const*, State>
	{
		return joinMap(std::move(_assignmentHere), std::move(_assignmentThere), State::join);
	});
	swap(m_assignments, newAssignments);
}

void RedundantAssignEliminator::changeUndecidedTo(string const& _variable, RedundantAssignEliminator::State _newState)
{
	for (auto& assignment: m_assignments[_variable])
		if (assignment.second == State{State::Undecided})
			assignment.second = _newState;
}

void AssignmentRemover::operator()(Block& _block)
{
	boost::range::remove_erase_if(_block.statements, [=](Statement const& _statement) -> bool {
		return _statement.type() == typeid(Assignment) && m_toRemove.count(&boost::get<Assignment>(_statement));
	});

	ASTModifier::operator()(_block);
}
