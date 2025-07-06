from .core import Goal, Sentence, Text, Message, Hypothesis
from .literate import COQ, Code, Comment, partition

#==========================================================================================================================#
#                                   Helper functions for the lsp ppstring format                                           #
#==========================================================================================================================#

def extract_string_from_ppcmd(ppcmd):
    """Extract string content from Ppcmd structures."""
    if ppcmd is None:
        return ""

    if isinstance(ppcmd, list) and len(ppcmd) >= 2 and ppcmd[0] == "Ppcmd_string":
        return ppcmd[1]

    if isinstance(ppcmd, list):
        if ppcmd and ppcmd[0] in ["Ppcmd_tag", "Ppcmd_box", "Ppcmd_glue"]:
            result = []
            for item in ppcmd[1:]:
                extracted = extract_string_from_ppcmd(item)
                if extracted:
                    result.append(extracted)
            return " ".join(result)

        all_strings = []
        for item in ppcmd:
            extracted = extract_string_from_ppcmd(item)
            if extracted:
                all_strings.append(extracted)
        return " ".join(all_strings)

    return ""

def extract_messages_from_data(messages_data):
    result = []
    if not messages_data:
        return result

    for msg in messages_data:
        if isinstance(msg, list) and len(msg) >= 2:
            content = extract_string_from_ppcmd(msg[1])
            if content:
                result.append(Message(contents=content))

    return result

def extract_hypothesis_from_ppcmd(hyp_ppcmd):
    if not hyp_ppcmd:
        return None

    full_str = extract_string_from_ppcmd(hyp_ppcmd)

    colon_count = full_str.count(':')

    if colon_count == 0:
        return Hypothesis(names=full_str.strip(), body=None, type="")

    elif colon_count == 1:
        name_part, type_part = full_str.split(':', 1)
        return Hypothesis(
            names=name_part.strip(),
            body=None,
            type=type_part.strip()
        )

    else:
        first_colon_index = full_str.find(':')
        last_colon_index = full_str.rfind(':')

        name_part = full_str[:first_colon_index]
        type_part = full_str[last_colon_index + 1:]

        body_part = full_str[first_colon_index + 1:last_colon_index]

        return Hypothesis(
            names=name_part.strip(),
            body=body_part.strip(),
            type=type_part.strip()
        )

def extract_hypotheses_list(hypotheses_data):
    result = []
    if not hypotheses_data:
        return result

    for hyp in hypotheses_data:
        hypothesis = extract_hypothesis_from_ppcmd(hyp)
        if hypothesis:
            result.append(hypothesis)

    return result

def extract_goal_from_data(goal_data, goal_id=None):
    """
    Extract a Goal object from goal data.
    """
    if not goal_data:
        return None

    conclusion = ""
    if "goal" in goal_data:
        conclusion = extract_string_from_ppcmd(goal_data["goal"])

    hypotheses = []
    if "hypotheses" in goal_data:
        hypotheses = extract_hypotheses_list(goal_data["hypotheses"])

    name = goal_id if goal_id is not None else goal_data.get("id", None)

    return Goal(name=name, conclusion=conclusion, hypotheses=hypotheses)

def extract_text(content_lines, start_pos, end_pos):
    start_line = start_pos['line']
    start_char = start_pos['character']
    end_line = end_pos['line']
    end_char = end_pos['character']

    if start_line >= len(content_lines):
        return ""

    if start_line == end_line:
        line = content_lines[start_line]
        start_char = min(start_char, len(line))
        end_char = min(end_char, len(line))
        return line[start_char:end_char]

    result = ""

    if start_line < len(content_lines):
        line = content_lines[start_line]
        start_char = min(start_char, len(line))
        result = line[start_char:]

    for line_num in range(start_line + 1, min(end_line, len(content_lines))):
        result += "\n" + content_lines[line_num]

    if end_line < len(content_lines):
        line = content_lines[end_line]
        end_char = min(end_char, len(line))
        result += "\n" + line[:end_char]

    return result

def process_proof_views(result_data, test_content):
    """Process proof views by properly mapping each command to its proof state."""
    fragments = []
    content_lines = test_content.split('\n')

    proof_views = result_data['proof_views']
    if not proof_views:
        return fragments

    previous_end = None

    for i, pv_data in enumerate(proof_views):
        position = pv_data["position"]
        start_pos = position["start"]
        end_pos = position["end"]

        if previous_end is not None:
            actual_start = previous_end
        else:
            actual_start = start_pos

        command_text = extract_text(content_lines, actual_start, end_pos)

        previous_end = end_pos

        goals = []
        proof_view = pv_data["proof_view"]
        if proof_view and proof_view.get('proof') and proof_view['proof']:
            goals_data = proof_view['proof'].get('goals', [])
            for goal_data in goals_data:
                goal = extract_goal_from_data(goal_data)
                if goal:
                    goals.append(goal)

        messages = []
        if proof_view and proof_view.get('messages'):
            messages_data = proof_view.get('messages', [])
            messages = extract_messages_from_data(messages_data)

        fragments.append(Sentence(
            contents=command_text.strip(),
            messages=messages,
            goals=goals
        ))

    return fragments

def is_embedded_comment(parts, comment_index):
    """Determine if a comment is embedded within code."""
    if comment_index < 0 or comment_index >= len(parts):
        return False

    has_code_before = False
    has_code_after = False

    # Check for code before the comment
    for i in range(0, comment_index):
        if isinstance(parts[i], Code) and str(parts[i].v).strip():
            has_code_before = True
            break

    # Check for code after the comment
    for i in range(comment_index + 1, len(parts)):
        if isinstance(parts[i], Code) and str(parts[i].v).strip():
            has_code_after = True
            break

    return has_code_before and has_code_after

def extract_comments_from_sentence(sentence):
    """Extract comments from a sentence, but keep embedded comments within their code."""
    parts = partition(COQ, sentence.contents)

    if len(parts) <= 1 or not any(isinstance(p, Comment) for p in parts): # type: ignore
        return [sentence]

    has_standalone_comment = False
    for i, part in enumerate(parts):
        if isinstance(part, Comment) and not is_embedded_comment(parts, i):
            has_standalone_comment = True
            break

    if not has_standalone_comment:
        return [sentence]

    result = []
    current_text = ""
    goals_assigned = False

    for i, part in enumerate(parts):
        if isinstance(part, Comment):
            if is_embedded_comment(parts, i):
                current_text += str(part.v)
            else:
                if current_text.strip():
                    if not goals_assigned:
                        result.append(Sentence(current_text, sentence.messages, sentence.goals))
                        goals_assigned = True
                    else:
                        result.append(Sentence(current_text, [], []))
                    current_text = ""

                result.append(Text(str(part.v)))
        else:
            current_text += str(part.v)

    if current_text.strip():
        if not goals_assigned:
            result.append(Sentence(current_text, sentence.messages, sentence.goals))
        else:
            result.append(Sentence(current_text, [], []))

    return result

def clean_fragment_contents(fragment):
    """Clean fragment contents without removing newlines."""
    if isinstance(fragment, Sentence):
        clean_content = fragment.contents.strip()
        return Sentence(
            contents=clean_content,
            messages=fragment.messages,
            goals=fragment.goals
        )
    elif isinstance(fragment, Text):
        clean_content = fragment.contents.strip()
        return Text(clean_content)
    else:
        return fragment

def pretty_print_fragments(fragments):
    """Pretty print fragments with clear formatting and indentation."""
    print("\n=== PRETTY PRINTED FRAGMENTS ===\n")

    for i, fragment in enumerate(fragments):
        if isinstance(fragment, Sentence):
            print(f"Fragment {i} [Sentence]:")

            content_lines = fragment.contents.split('\n')
            for line in content_lines:
                print(f"  │ {line}")

            if fragment.messages:
                print("  ├─ Messages:")
                for j, msg in enumerate(fragment.messages):
                    print(f"  │  {j}: {msg.contents}")
            else:
                print("  ├─ Messages: None")

            if fragment.goals:
                print("  └─ Goals:")
                for j, goal in enumerate(fragment.goals):
                    print(f"  │  Goal {j} ({goal.name}):")
                    print(f"  │    Conclusion: {goal.conclusion}")

                    if goal.hypotheses:
                        print(f"  │    Hypotheses:")
                        for k, hyp in enumerate(goal.hypotheses):
                            if hyp.body:
                                print(f"  │      {hyp.names}: {hyp.body} : {hyp.type}")
                            else:
                                print(f"  │      {hyp.names}: {hyp.type}")
                    else:
                        print(f"  │    Hypotheses: None")
            else:
                print("  └─ Goals: None")

        elif isinstance(fragment, Text):
            print(f"Fragment {i} [Comment]:")

            content_lines = fragment.contents.split('\n')
            for line in content_lines:
                if line.strip():
                    print(f"  │ {line}")

        print("\n" + "─" * 60 + "\n")
