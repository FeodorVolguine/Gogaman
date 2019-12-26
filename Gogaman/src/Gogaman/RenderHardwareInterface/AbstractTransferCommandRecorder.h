#pragma once

#include "Gogaman/Core/CRTP.h"

#include "CommandBuffer.h"

namespace Gogaman
{
	namespace RHI
	{
		class CommandBuffer;

		template<typename ImplementationType>
		class AbstractTransferCommandRecorder : public CRTP<ImplementationType, AbstractTransferCommandRecorder>
		{
		public:
			AbstractTransferCommandRecorder(const AbstractTransferCommandRecorder &) = delete;
			AbstractTransferCommandRecorder(AbstractTransferCommandRecorder &&)      = delete;

			AbstractTransferCommandRecorder &operator=(const AbstractTransferCommandRecorder &) = delete;
			AbstractTransferCommandRecorder &operator=(AbstractTransferCommandRecorder &&)      = delete;

			inline void StopRecording() { m_CommandBuffer->StopRecording(); }
		private:
			AbstractTransferCommandRecorder(CommandBuffer *commandBuffer)
				: m_CommandBuffer(commandBuffer)
			{
				m_CommandBuffer->StartRecording();
			}

			~AbstractTransferCommandRecorder() = default;
		protected:
			CommandBuffer *m_CommandBuffer;
		private:
			friend ImplementationType;
		};
	}
}