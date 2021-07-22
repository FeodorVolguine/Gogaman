#pragma once

#include "Gogaman/Utilities/Algorithm/DirectedGraph.h"

#include "IntermediateRepresentation.h"

namespace Gogaman
{
	namespace FlexShader
	{
		namespace IR
		{
			class SSA
			{
			public:
				using Block = std::vector<uint32_t>;
			public:
				SSA(const IR &intermediateRepresentation);
				~SSA() = default;

				inline const IR &GetIR() const { return m_IR;}

				inline const std::vector<Block> &GetBasicBlocks() const { return m_BasicBlocks; }
			private:
				struct PhiFunction
				{
					std::unordered_map<uint16_t, Address> parameters;
					Address definedVariable;
				};
			private:
				void EliminateRedunantBranches();

				void BuildControlFlowGraph();

				//lhs or rhs of assignment
				template<bool checkAssignment = false>
				bool ContainsVariable(const Instruction &instruction, const Address variable) const
				{
					const auto CheckAddress = [&](const Address address)
					{
						switch(address.GetType())
						{
						case Address::Type::Variable:
							return address == variable;
						case Address::Type::Function:
							return false;
							//May need to handle vectors
						case Address::Type::ConstantOrVector:
							return false;
						case Address::Type::InstructionPointer:
							return ContainsVariable(m_IR.instructions[address.GetValue()], variable);
						}
					};

					//Arithmetic operator
					if((uint8_t)instruction.operation <= 9U)
						return CheckAddress(instruction.address1) || CheckAddress(instruction.address2);

					switch(instruction.operation)
					{
					case Operation::VariableDeclaration:
					case Operation::VectorSwizzle:
						return instruction.address1 == variable;
					case Operation::Subscript:
						//TODO: Handle this once subscripts implemented
						return false;
					case Operation::Assignment:
							return checkAssignment ? CheckAddress(instruction.address1) : CheckAddress(instruction.address2);
					}
				}

				void RenameVariables(std::vector<std::vector<PhiFunction>> &blockPhiFunctions, const std::vector<std::vector<uint16_t>> &dominatorChildren, std::unordered_map<Address, Address, HashAddress> &originalVariableAddresses, uint16_t blockIndex, std::vector<std::stack<Address>> &variableVersions);

				void RenameVariable(std::unordered_map<Address, Address, HashAddress> &originalVariableAddresses, std::vector<std::stack<Address>> &variableVersions, Address &variable);
			private:
				IR                      m_IR;
				DirectedGraph<uint16_t> m_ControlFlowGraph;
				//std::vector<std::pair<uint32_t, uint32_t>> m_BasicBlocks;
				std::vector<Block>      m_BasicBlocks;
			};

			inline void LogSSA(const SSA &ssa)
			{
				for(uint32_t i = 0; i < ssa.GetBasicBlocks().size(); i++)
				{
					const SSA::Block &block = ssa.GetBasicBlocks()[i];
					GM_LOG_CORE_INFO("Block %d", i);

					for(uint32_t j : block)
					{
						const Instruction &instruction = ssa.GetIR().instructions[j];
						if(instruction.address1.IsValid())
						{
							if(instruction.address2.IsValid())
							{
								GM_LOG_CORE_INFO("	%d: %s | Address 1: %s | Address 2: %s", j, GetOperationString(instruction.operation).c_str(), AddressString(instruction.address1).c_str(), AddressString(instruction.address2).c_str());
							}
							else
								GM_LOG_CORE_INFO("	%d: %s | Address 1: %s", j, GetOperationString(instruction.operation).c_str(), AddressString(instruction.address1).c_str());
						}
						else
							GM_LOG_CORE_INFO("	%d: %s", j, GetOperationString(instruction.operation).c_str());	
					}
				}
			}
		}
	}
}