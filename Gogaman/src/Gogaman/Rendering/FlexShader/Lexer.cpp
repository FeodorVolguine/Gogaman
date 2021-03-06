#include "pch.h"
#include "Lexer.h"

#include "Gogaman/Core/Base.h"

#include "Token.h"

namespace Gogaman
{
	namespace FlexShader
	{
		std::vector<Token> Lex(const std::string &source)
		{
			std::vector<Token> tokens;
	
			uint16_t lineCount = 1;

			uint32_t cursorPosition = 0;
			while(cursorPosition < source.length())
			{
				const char character = source[cursorPosition];

				auto AddToken = [&](const Token::Type type, std::string_view &&lexeme)
				{
					Token &token = tokens.emplace_back();
					token.type   = type;
					token.line   = lineCount;
					token.lexeme = std::move(lexeme);
				};
	
				auto AddAtom = [&](const Token::Type type) { AddToken(type, std::string_view(source.c_str() + cursorPosition, 1)); };

				//New line
				if(character == '\n')
				{
					lineCount++;
					cursorPosition++;
					continue;
				}

				//White-space
				if(isspace(character))
				{
					cursorPosition++;
					continue;
				}

				//Single-line comment
				if((character == '/') && (source[cursorPosition + 1] == '/'))
				{
					cursorPosition += 2;

					while(source[cursorPosition] != '\n')
						cursorPosition++;

					cursorPosition++;
					continue;
				}

				//Multi-line comment
				if((character == '/') && (source[cursorPosition + 1] == '*'))
				{
					cursorPosition += 2;

					while(true)
					{
						if((source[cursorPosition] == '*') && (source[cursorPosition + 1] == '/'))
							break;

						if(source[cursorPosition] == '\n')
							lineCount++;

						cursorPosition++;
					}

					cursorPosition += 2;
					continue;
				}
	
				if(isdigit(character))
				{
					Token::Type literalType = Token::Type::IntegerLiteral;
					const uint32_t initialPosition = cursorPosition;
					while(true)
					{
						cursorPosition++;

						if(source[cursorPosition] == '.')
						{
							literalType = Token::Type::FloatingPointLiteral;
							while(true)
							{
								cursorPosition++;
								if(!isdigit(source[cursorPosition]))
									break;
							}
						}
	
						if(!isdigit(source[cursorPosition]))
							break;
					}
	
					AddToken(literalType, std::string_view(source.c_str() + initialPosition, cursorPosition - initialPosition));
					if((literalType == Token::Type::FloatingPointLiteral) && ((source[cursorPosition] == 'f') || (source[cursorPosition] == 'F')))
						cursorPosition++;

					continue;
				}

				if(character == '"')
				{
					const uint32_t initialPosition = cursorPosition;

					//replace this loop with find_last_of(")
					/*
					auto GetExtension = [](const std::string &filepath)
					{
						const auto periodIndex = filepath.find_last_of('.');
						return filepath.substr(periodIndex + 1);
					};

					if(GetExtension(i) == "flex")
					*/
					while(true)
					{
						cursorPosition++;

						//GM_DEBUG_ASSERT(cursorPosition < source.length(), "Failed to tokenize FlexShader");

						if(source[cursorPosition] == '"')
							break;
					}

					AddToken(Token::Type::StringLiteral, std::string_view(source.c_str() + initialPosition + 1, cursorPosition - (initialPosition + 1)));
					cursorPosition++;
					continue;
				}
	
				if(isalpha(character) || character == '_')
				{
					const uint32_t initialPosition = cursorPosition;
	
					while(true)
					{
						cursorPosition++;
	
						if(!isalnum(source[cursorPosition]) && source[cursorPosition] != '_')
							break;
					}

					std::string_view characters(source.c_str() + initialPosition, cursorPosition - initialPosition);
					
					if((characters == "true") || (characters == "false"))
					{
						AddToken(Token::Type::BooleanLiteral, std::move(characters));
						continue;
					}

					bool isKeyword = false;
					const std::vector<std::string> keywords = { "void", "bool", "int", "float", "float2", "float3", "float4", "Sampler", "input", "output", "component", "if", "else", "return" };
					for(const auto &i : keywords)
					{
						if(characters == i)
						{
							AddToken(Token::Type::Keyword, std::move(characters));
							isKeyword = true;
							break;
						}
					}

					if(!isKeyword)
						AddToken(Token::Type::Identifier, std::move(characters));

					continue;
				}

				if(character == '=')
				{
					if(source[++cursorPosition] == '=')
					{
						AddAtom(Token::Type::Equality);
						cursorPosition++;
					}
					else
						AddAtom(Token::Type::Assignment);
					
					continue;
				}

				if(character == '!')
				{
					if(source[++cursorPosition] == '=')
					{
						AddAtom(Token::Type::Inequality);
						cursorPosition++;
					}
					//else
						//AddAtom(Token::Type::LogicalNot);

					continue;
				}

				switch(character)
				{
				case ',':
					AddAtom(Token::Type::Comma);
					break;
				case '.':
					AddAtom(Token::Type::Dot);
					break;
				case '/':
					AddAtom(Token::Type::Slash);
					break;
				case ':':
					AddAtom(Token::Type::Colon);
					break;
				case ';':
					AddAtom(Token::Type::Semicolon);
					break;
				case '%':
					AddAtom(Token::Type::Percent);
					break;
				case '*':
					AddAtom(Token::Type::Asterisk);
					break;
				case '(':
					AddAtom(Token::Type::LeftParenthesis);
					break;
				case ')':
					AddAtom(Token::Type::RightParenthesis);
					break;
				case '[':
					AddAtom(Token::Type::LeftSquareBracket);
					break;
				case ']':
					AddAtom(Token::Type::RightSquareBracket);
					break;
				case '{':
					AddAtom(Token::Type::LeftBrace);
					break;
				case '}':
					AddAtom(Token::Type::RightBrace);
					break;
				case '<':
					AddAtom(Token::Type::Less);
					break;
				case '>':
					AddAtom(Token::Type::Greater);
					break;
				case '+':
					AddAtom(Token::Type::Plus);
					break;
				case '-':
					AddAtom(Token::Type::Minus);
					break;
				default:
					GM_DEBUG_ASSERT(false, "Failed to tokenize FlexShader | Line %d | Character \"%c\" is invalid", lineCount, character);
					break;
				}

				cursorPosition++;
			}
	
			return tokens;
		}
	}
}