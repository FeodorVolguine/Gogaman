#include "pch.h"
#include "WindowsInput.h"

#include "Gogaman/Core/Application.h"

#include <GLFW/glfw3.h>

namespace Gogaman
{
	bool WindowsInput::IsKeyPressed(const int scancode)
	{
		auto window   = static_cast<GLFWwindow *>(Application::GetInstance().GetWindow().GetNativeWindow());
		auto keyState = glfwGetKey(window, scancode);

		return keyState == GLFW_PRESS || keyState == GLFW_REPEAT;
	}

	bool WindowsInput::IsMouseButtonPressed(const int scancode)
	{
		auto window      = static_cast<GLFWwindow *>(Application::GetInstance().GetWindow().GetNativeWindow());
		auto buttonState = glfwGetMouseButton(window, scancode);

		return buttonState == GLFW_PRESS;
	}

	const glm::vec2 WindowsInput::GetMousePosition()
	{
		auto window = static_cast<GLFWwindow *>(Application::GetInstance().GetWindow().GetNativeWindow());

		glm::dvec2 mousePosition;
		glfwGetCursorPos(window, &mousePosition.x, &mousePosition.y);
		return mousePosition;
	}
}