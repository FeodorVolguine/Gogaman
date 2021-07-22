#include "pch.h"
#include "StaticSingleAssignment.h"

#define FLEX_SHADER_IS_BRANCH_INSTRUCTION(x) ((x.operation == Operation::Branch) || (x.operation == Operation::BranchOnNotEqual))

namespace Gogaman
{
	namespace FlexShader
	{
		namespace IR
		{
			SSA::SSA(const IR &intermediateRepresentation)
				: m_IR(intermediateRepresentation)
			{
				EliminateRedunantBranches();

				GM_LOG_CORE_INFO("_");
				GM_LOG_CORE_INFO("Intermediate representation after eliminating redundant branches");
				LogIR(m_IR);

				BuildControlFlowGraph();

				//Build flattened dominator tree
				const std::vector<uint16_t> postOrder = m_ControlFlowGraph.PostOrder(0);

				std::vector<uint16_t> postOrderIndices;
				postOrderIndices.resize(postOrder.size());
				for(auto i = 0; i < postOrder.size(); i++)
					postOrderIndices[postOrder[i]] = i;

				constexpr uint16_t undefinedDominator = UINT16_MAX;
				std::vector<uint16_t> dominators(m_ControlFlowGraph.GetVertexCount(), undefinedDominator);

				dominators[postOrderIndices[0]] = postOrderIndices[0];
				bool changed = true;
				while(changed)
				{
					changed = false;
					for(auto i = postOrder.rbegin() + 1; i != postOrder.rend(); i++)
					{
						const std::vector<uint16_t> predecessors = m_ControlFlowGraph.IncomingConnections(*i);

						uint16_t firstProcessedPredecessorIndex;
						for(firstProcessedPredecessorIndex = 0; firstProcessedPredecessorIndex < predecessors.size(); firstProcessedPredecessorIndex++)
							if(dominators[postOrderIndices[predecessors[firstProcessedPredecessorIndex]]] != undefinedDominator)
								break;

						uint16_t newImmediateDominator = postOrderIndices[predecessors[firstProcessedPredecessorIndex]];
						for(uint16_t j = firstProcessedPredecessorIndex + 1; j < predecessors.size(); j++)
							if(dominators[postOrderIndices[predecessors[j]]] != undefinedDominator)
							{
								uint16_t index1 = postOrderIndices[predecessors[j]];
								uint16_t index2 = newImmediateDominator;
								while(index1 != index2)
								{
									while(index1 < index2)
										index1 = dominators[index1];
									while(index2 < index1)
										index2 = dominators[index2];
								}

								newImmediateDominator = index1;
							}

						if(dominators[postOrderIndices[*i]] != newImmediateDominator)
						{
							dominators[postOrderIndices[*i]] = newImmediateDominator;
							changed = true;
						}
					}
				}

				//for(auto i = 0; i < dominators.size(); i++)
					//GM_LOG_CORE_INFO("Immediate dominator of node %d: %d", postOrder[i], postOrder[dominators[i]]);

				//Build dominator tree
				std::vector<std::vector<uint16_t>> dominatorChildren(m_ControlFlowGraph.GetVertexCount());
				//Skip last because first block should not have any children (dominator array says entry node is its own dominator)
				for(auto i = 0; i < dominators.size() - 1; i++)
					dominatorChildren[postOrder[dominators[i]]].emplace_back(postOrder[i]);

				//Calculate dominance frontiers
				std::vector<std::set<uint16_t>> dominanceFrontiers;
				dominanceFrontiers.resize(m_ControlFlowGraph.GetVertexCount());
				for(uint16_t i = 0; i < m_ControlFlowGraph.GetVertexCount(); i++)
				{
					const std::vector<uint16_t> predecessors = m_ControlFlowGraph.IncomingConnections(i);

					if(predecessors.size() > 1)
						for(const uint16_t j : predecessors)
						{
							uint16_t runner = postOrderIndices[j];
							//while(runner != dominators[i])
							while(runner != dominators[postOrderIndices[i]])
							{
								dominanceFrontiers[runner].emplace(i);
								runner = dominators[runner];
							}
						}
				}
				/*
				for(auto i = 0; i < dominanceFrontiers.size(); i++)
				{
					GM_LOG_CORE_INFO("Dominance frontiers of node %d:", postOrder[i]);
					for(auto j : dominanceFrontiers[i])
						GM_LOG_CORE_INFO("	%d", j);
				}*/

				std::unordered_map<Address, Address, HashAddress> originalVariableAddresses;
				
				//Identify phi functions
				std::vector<std::vector<PhiFunction>> blockPhiFunctions(m_BasicBlocks.size());
				for(uint16_t i = 0; i < m_BasicBlocks.size(); i++)
				{
					for(const uint32_t x : m_BasicBlocks[i])
					{
						Instruction &currentInstruction = m_IR.instructions[x];
						if(currentInstruction.operation == Operation::Assignment)
						{
							//Assumption: LHS of assignment is always either variable address, variable declaration instruction, or swizzle instruction
							GM_DEBUG_ASSERT((currentInstruction.address1.GetType() == Address::Type::Variable) || (currentInstruction.address1.GetType() == Address::Type::InstructionPointer), "Failed to generate FlexShader SSA phi functions | Invalid assignment instruction");
							Address definedVariable = (currentInstruction.address1.GetType() == Address::Type::Variable) ? currentInstruction.address1 : m_IR.instructions[currentInstruction.address1.GetValue()].address1;

							const auto IsBlockUsingVariable = [&](const uint16_t blockIndex, const Address address)
							{
								for(uint32_t j : m_BasicBlocks[blockIndex])
									if((m_IR.instructions[j].operation == Operation::Assignment) || (m_IR.instructions[j].operation == Operation::FunctionParameter))
										if(ContainsVariable(m_IR.instructions[j], address))
											return true;

								return false;
							};

							for(const uint16_t j : dominanceFrontiers[postOrderIndices[i]])
								if(IsBlockUsingVariable(j, definedVariable))
								{
									bool foundExistingPhiFunction = false;
									for(PhiFunction &k : blockPhiFunctions[j])
										if(k.definedVariable == definedVariable)
										{
											k.parameters[i] = definedVariable;
											foundExistingPhiFunction = true;
										}

									if(!foundExistingPhiFunction)
									{
										PhiFunction &phiFunction = blockPhiFunctions[j].emplace_back();
										phiFunction.definedVariable = definedVariable;
										phiFunction.parameters[i] = definedVariable;
									}
								}
						}
						else if(currentInstruction.operation == Operation::VariableDeclaration)
							originalVariableAddresses[currentInstruction.address1] = currentInstruction.address1;
					}
				}

				//Rename variables
				//std::vector<std::stack<Address>> variableVersions(m_IR.variableSpecifiers.size());
				//RenameVariables(blockPhiFunctions, dominatorChildren, originalVariableAddresses, 0, variableVersions);

				GM_LOG_CORE_INFO("_");
				GM_LOG_CORE_INFO("Intermediate representation after variable renaming");
				LogSSA(*this);
			}

			void SSA::EliminateRedunantBranches()
			{
				for(uint32_t i = 0; i < m_IR.executionOrder.size(); i++)
				{
					const uint32_t instructionIndex = m_IR.executionOrder[i];
					auto &instruction = m_IR.instructions[instructionIndex];

					if(instruction.operation == Operation::Branch)
					{
						const auto &targetInstruction = m_IR.instructions[instruction.address1.GetValue()];
						if(targetInstruction.operation == Operation::Branch)
							instruction.address1 = targetInstruction.address1;
					}
				}
			}

			void SSA::BuildControlFlowGraph()
			{
				std::unordered_map<uint32_t, uint32_t> instructionExecutionIndices;
				instructionExecutionIndices.reserve(m_IR.executionOrder.size());
				for(uint32_t i = 0; i < m_IR.executionOrder.size(); i++)
					instructionExecutionIndices[m_IR.executionOrder[i]] = i;

				const auto IsBranching = [](const Instruction &instruction) { return (instruction.operation == Operation::Branch) || (instruction.operation == Operation::BranchOnNotEqual); };

				//Generate leaders
				std::set<uint32_t> leaders;
				leaders.emplace(0);
				bool previousInstructionWasBranch = IsBranching(m_IR.instructions[m_IR.executionOrder[0]]);
				for(auto i = 1; i < m_IR.executionOrder.size(); i++)
				{
					if(previousInstructionWasBranch)
						leaders.emplace(i);

					const Instruction &instruction = m_IR.instructions[m_IR.executionOrder[i]];
					if(IsBranching(instruction))
					{
						if(instruction.operation == Operation::Branch)
							leaders.emplace(instructionExecutionIndices[instruction.address1.GetValue()]);
						else if(instruction.operation == Operation::BranchOnNotEqual)
							leaders.emplace(instructionExecutionIndices[instruction.address2.GetValue()]);
						
						previousInstructionWasBranch = true;
					}
					else
						previousInstructionWasBranch = false;
				}

				//Generate basic blocks
				std::unordered_map<uint32_t, uint32_t> leaderBlockIndices;
				leaderBlockIndices.reserve(leaders.size());
				while(!leaders.empty())
				{
					const uint32_t blockStart = *leaders.begin();
					leaders.erase(leaders.begin());

					uint32_t blockEnd = blockStart;
					for(uint32_t i = blockStart + 1; (i < m_IR.executionOrder.size()) && !leaders.contains(i); i++)
						blockEnd = i;

					leaderBlockIndices[blockStart] = m_BasicBlocks.size();
					m_BasicBlocks.emplace_back(Block(m_IR.executionOrder.begin() + blockStart, m_IR.executionOrder.begin() + blockEnd + 1));
					m_ControlFlowGraph.CreateVertex();
				}

				//Create graph edges
				for(uint16_t i = 0; i < m_BasicBlocks.size(); i++)
				{
					const uint32_t endInstructionExecutionIndex = m_BasicBlocks[i].back();
					const Instruction &endInstruction = m_IR.instructions[endInstructionExecutionIndex];
					if(endInstruction.operation == Operation::Branch)
						m_ControlFlowGraph.CreateEdge(i, leaderBlockIndices[instructionExecutionIndices[endInstruction.address1.GetValue()]]);
					else if(endInstruction.operation == Operation::BranchOnNotEqual)
					{
						m_ControlFlowGraph.CreateEdge(i, leaderBlockIndices[instructionExecutionIndices[endInstruction.address2.GetValue()]]);
						if(i + 1 < m_BasicBlocks.size())
							m_ControlFlowGraph.CreateEdge(i, i + 1);
					}
					else if((endInstructionExecutionIndex + 1) != m_IR.executionOrder.size())
						m_ControlFlowGraph.CreateEdge(i, leaderBlockIndices[endInstructionExecutionIndex + 1]);
				}
			}

			void SSA::RenameVariables(std::vector<std::vector<PhiFunction>> &blockPhiFunctions, const std::vector<std::vector<uint16_t>> &dominatorChildren, std::unordered_map<Address, Address, HashAddress> &originalVariableAddresses, uint16_t blockIndex, std::vector<std::stack<Address>> &variableVersions)
			{
				std::vector<Address> renamedVariables;

				for(auto &i : blockPhiFunctions[blockIndex])
				{
					RenameVariable(originalVariableAddresses, variableVersions, i.definedVariable);
					//Insert variable declaration instruction? (is it needed for phi functions?)
					renamedVariables.emplace_back(i.definedVariable);
				}

				for(uint32_t i = 0; i < m_BasicBlocks[blockIndex].size(); i++)
				{
					Instruction &currentInstruction = m_IR.instructions[i];

					//TODO Replace all variable uses with latest version (binary ops)
					if(currentInstruction.operation == Operation::FloatMultiply)
						currentInstruction.address1 = variableVersions[originalVariableAddresses[currentInstruction.address1].GetValue()].top();

					if(currentInstruction.operation == Operation::Assignment)
					{
						//Gather all variables in RHS of asmnt and replace them with latest version here...

						//Assumption: LHS of assignment is always either variable address, variable declaration instruction, or swizzle instruction
						GM_DEBUG_ASSERT((currentInstruction.address1.GetType() == Address::Type::Variable) || (currentInstruction.address1.GetType() == Address::Type::InstructionPointer), "Failed to generate FlexShader SSA phi functions | Invalid assignment instruction");
						Address &definedVariable = (currentInstruction.address1.GetType() == Address::Type::Variable) ? currentInstruction.address1 : m_IR.instructions[currentInstruction.address1.GetValue()].address1;
						RenameVariable(originalVariableAddresses, variableVersions, definedVariable);

						//Insert variable declaration instruction
						m_BasicBlocks[blockIndex].insert(m_BasicBlocks[blockIndex].begin() + i++, m_IR.instructions.size());
						m_IR.instructions.emplace_back(Operation::VariableDeclaration, definedVariable);
						renamedVariables.emplace_back(m_IR.instructions.back().address1);
					}
				}

				for(uint16_t i : m_ControlFlowGraph.OutgoingConnections(blockIndex))
					for(auto &j : blockPhiFunctions[i])
						j.parameters[blockIndex] = variableVersions[originalVariableAddresses[j.parameters[blockIndex]].GetValue()].top();

				for(uint16_t i : dominatorChildren[blockIndex])
					RenameVariables(blockPhiFunctions, dominatorChildren, originalVariableAddresses, i, variableVersions);

				for(Address i : renamedVariables)
					variableVersions[originalVariableAddresses[i].GetValue()].pop();
			}

			void SSA::RenameVariable(std::unordered_map<Address, Address, HashAddress> &originalVariableAddresses, std::vector<std::stack<Address>> &variableVersions, Address &variable)
			{
				const Address originalVariable = variable;
				//New variable version
				variable = Address(Address::Type::Variable, m_IR.variableSpecifiers.size(), variable.GetDataType());
				//Variable specifier
				m_IR.variableSpecifiers.emplace_back(m_IR.variableSpecifiers[originalVariable.GetValue()]);

				GM_LOG_CORE_INFO("Renaming variable %s to %s", AddressString(originalVariable).c_str(), AddressString(variable).c_str());

				originalVariableAddresses[variable] = originalVariable;

				//Push new version as the most recent definition
				variableVersions[originalVariable.GetValue()].emplace(variable);
			}
		}
	}
}