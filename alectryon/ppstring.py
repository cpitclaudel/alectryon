from .core import Goal, Message, Hypothesis

#==========================================================================================================================#
#                                   Helper functions for the lsp ppstring format                                           #
#==========================================================================================================================#

def string_of_pp_string(pp):
    """Convert a Coq pretty-printed string to a regular string"""
    if not isinstance(pp, list) or len(pp) == 0:
        return str(pp) if pp else ""

    match pp[0]:
        case "Ppcmd_empty":
            return ""
        case "Ppcmd_string":
            return pp[1] if len(pp) > 1 else ""
        case "Ppcmd_glue":
            if len(pp) > 1 and isinstance(pp[1], list):
                return "".join(string_of_pp_string(sub_pp) for sub_pp in pp[1])
            return ""
        case "Ppcmd_box":
            return string_of_pp_string(pp[2]) if len(pp) > 2 else ""
        case "Ppcmd_tag":
            return string_of_pp_string(pp[2]) if len(pp) > 2 else ""
        case "Ppcmd_print_break":
            return " " * pp[1] if len(pp) > 1 and isinstance(pp[1], int) else ""
        case "Ppcmd_force_newline":
            return "\n"
        case "Ppcmd_comment":
            if len(pp) > 1 and isinstance(pp[1], list):
                return " ".join(pp[1])
            return ""
        case _:
            return str(pp)

def extract_goals_and_messages_from_proof_views(proof_views):
    """Extract only goals and messages from proof views"""
    results = []

    for pv_data in proof_views:
        proof_view = pv_data["proof_view"]

        # Extract goals
        goals = []
        if proof_view and proof_view.get('proof') and proof_view['proof']:
            goals_data = proof_view['proof'].get('goals', [])
            for goal_data in goals_data:
                goal = extract_goal_from_data(goal_data)
                if goal:
                    goals.append(goal)

        # Extract messages
        messages = []
        if proof_view and proof_view.get('messages'):
            messages_data = proof_view.get('messages', [])
            for msg in messages_data:
                if isinstance(msg, list) and len(msg) >= 2:
                    content = string_of_pp_string(msg[1])
                    if content:
                        messages.append(Message(contents=content))

        results.append({
            'goals': goals,
            'messages': messages
        })

    return results

def extract_goal_from_data(goal_data, goal_id=None):
    """Extract a Goal object from goal data"""
    if not goal_data:
        return None

    conclusion = ""
    if "goal" in goal_data:
        conclusion = string_of_pp_string(goal_data["goal"])

    hypotheses = []
    if "hypotheses" in goal_data:
        for hyp in goal_data["hypotheses"]:
            full_str = string_of_pp_string(hyp)

            colon_count = full_str.count(':')

            if colon_count == 0:
                hypothesis = Hypothesis(names=[full_str.strip()], body=None, type="")
            elif colon_count == 1:
                name_part, type_part = full_str.split(':', 1)
                hypothesis = Hypothesis(
                    names=[name_part.strip()],
                    body=None,
                    type=type_part.strip()
                )
            else:
                first_colon_index = full_str.find(':')
                last_colon_index = full_str.rfind(':')

                name_part = full_str[:first_colon_index]
                type_part = full_str[last_colon_index + 1:]
                body_part = full_str[first_colon_index + 1:last_colon_index]

                hypothesis = Hypothesis(
                    names=[name_part.strip()],
                    body=body_part.strip(),
                    type=type_part.strip()
                )

            if hypothesis:
                hypotheses.append(hypothesis)

    name = goal_id if goal_id is not None else goal_data.get("id", None)

    return Goal(name=name, conclusion=conclusion, hypotheses=hypotheses)
