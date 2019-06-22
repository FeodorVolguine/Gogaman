#pragma once

#include "pch.h"
#include "Gogaman/Graphics/RenderingContext.h"

namespace Gogaman
{
	class Window
	{
	public:
		Window(const char *title, const int width, const int height)
			: m_Title(title), m_Width(width), m_Height(height), m_VerticalSynchronization(true)
		{}

		virtual ~Window()
		{}

		static Window *Create(const char *title, const int width, const int height);

		virtual void Update() = 0;
		static  void Shutdown();

		virtual void *GetNativeWindow() const = 0;

		virtual void EnableVerticalSync()  = 0;
		virtual void DisableVerticalSync() = 0;
		inline  bool IsVerticalSynchronizationEnabled() const { return m_VerticalSynchronization; }

		inline const char *GetTitle() const { return m_Title; }

		inline int GetWidth()  const { return m_Width;  }
		inline int GetHeight() const { return m_Height; }
	protected:
		const char *m_Title;

		int  m_Width;
		int  m_Height;

		bool m_VerticalSynchronization;

		std::unique_ptr<RenderingContext> m_RenderingContext;
	};
}