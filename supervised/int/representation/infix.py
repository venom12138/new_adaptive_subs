import string

from metric_logging import log_text
from supervised.int.representation import base
from third_party.INT.visualization import seq_parse

CONDITION_LEXEME = '&'
OBJECTIVE_LEXEME = '#'
DESTINATION_LEXEME = '|'
PADDING_LEXEME = '_'
EOS_LEXEME = '$'
OUTPUT_START_LEXEME = '@'
BOS_LEXEME = '?'


MULTI_CHAR_LEXEMES = [
    '1/',
    '^2',
    'sqrt',
    r'\leq ',
    r'\geq ',
    r'\gt ',
    r'\lt ',
    # We haven't use inequalities in INT yet, so not sure if '\leq' and '\geq'
    # work properly.
]

VOCABULARY = (
        [
            BOS_LEXEME,
            PADDING_LEXEME,
            EOS_LEXEME,
            OUTPUT_START_LEXEME,
            OBJECTIVE_LEXEME,
            DESTINATION_LEXEME,
            CONDITION_LEXEME,
            '=',
            '(',
            ')',
            '*',
            '+',
            '-',  # both subtraction and unary minus
            '^',
        ] +
        [str(i) for i in range(11)] + 
        list(string.ascii_lowercase) +
        MULTI_CHAR_LEXEMES
)


TOKEN_TO_STR = dict(list(enumerate(VOCABULARY)))
STR_TO_TOKEN = {str_: token for token, str_ in TOKEN_TO_STR.items()}
assert len(TOKEN_TO_STR) == len(STR_TO_TOKEN), \
    "There are some duplicated lexemes in vocabulary."

assert STR_TO_TOKEN[BOS_LEXEME] == 0
assert STR_TO_TOKEN[PADDING_LEXEME] == 1
assert STR_TO_TOKEN[EOS_LEXEME] == 2
assert STR_TO_TOKEN[OUTPUT_START_LEXEME] == 3
# print(f"len(TOKEN_TO_STR):{len(TOKEN_TO_STR)}")
assert len(TOKEN_TO_STR) == 58 # 46


def split_expression_on_lexeme(expr, lexeme):
    subexprs = []
    expr_beg = 0

    lexeme_beg = expr.find(lexeme, expr_beg)
    while lexeme_beg != -1:
        if lexeme_beg > expr_beg:
            subexprs.append(expr[expr_beg:lexeme_beg])

        lexeme_end = lexeme_beg + len(lexeme)
        subexprs.append(expr[lexeme_beg:lexeme_end])

        expr_beg = lexeme_end
        lexeme_beg = expr.find(lexeme, expr_beg)

    if expr_beg < len(expr):
        subexprs.append(expr[expr_beg:])

    return subexprs


def split_formula_to_lexemes(formula):
    subexprs = [formula]
    # We split the formula on every occurrence of any MULTI_CHAR_LEXEME
    for lexeme in MULTI_CHAR_LEXEMES:
        next_subexprs = []
        for subexpr in subexprs:
            next_subexprs += (
                [subexpr] if subexpr in VOCABULARY
                else split_expression_on_lexeme(subexpr, lexeme)
            )
        subexprs = next_subexprs

    lexemes = []
    for subexpr in subexprs:
        lexemes += (
            [subexpr] if subexpr in VOCABULARY
            else list(subexpr)  # treat every char as a separate lexeme
        )
    return lexemes


class InfixRepresentation(base.Representation):
    token_consts = base.TokenConsts(
        num_tokens=len(STR_TO_TOKEN),
        padding_token=STR_TO_TOKEN[PADDING_LEXEME],
        output_start_token=STR_TO_TOKEN[OUTPUT_START_LEXEME],
    )

    @staticmethod
    def proof_state_to_input_formula(state, add_input_end_lexeme=True):
        conditions = [
            seq_parse.logic_statement_to_seq_string(condition)
            for condition in state['observation']['ground_truth']
        ]
        # most likely only one objective
        objectives = [
            seq_parse.logic_statement_to_seq_string(objective)
            for objective in state['observation']['objectives']
        ]
        formula = OBJECTIVE_LEXEME + OBJECTIVE_LEXEME.join(objectives)
        if len(conditions) > 0:
            formula += CONDITION_LEXEME + CONDITION_LEXEME.join(conditions)
        if add_input_end_lexeme:
            formula += EOS_LEXEME
        
        return formula

    @staticmethod
    def proof_states_to_policy_input_formula(self, current_state, destination_state):

        formula = self.proof_state_to_input_formula(current_state, False)
        destination_objectives = [seq_parse.logic_statement_to_seq_string(objective)
            for objective in destination_state['observation']['objectives']
        ]
        dede = DESTINATION_LEXEME
        formula += DESTINATION_LEXEME + DESTINATION_LEXEME.join(destination_objectives)
        formula += EOS_LEXEME
        return formula

    @staticmethod
    def proof_state_to_target_formula(state):
        target_objectives = [
            seq_parse.logic_statement_to_seq_string(objective)
            for objective in state['observation']['objectives']
        ]
        return OUTPUT_START_LEXEME + OBJECTIVE_LEXEME.join(target_objectives) + EOS_LEXEME

    @staticmethod
    def tokenize_formula(formula):
        lexemes = split_formula_to_lexemes(formula)
        try:
            return [STR_TO_TOKEN[lexeme] for lexeme in lexemes]
        except KeyError as e:
            log_text(
                "Error",
                "Tokenization error - unrecognized lexeme."
                f"Formula split to lexemes:\n{lexemes}"
            )
            raise e

    @staticmethod
    def formula_from_tokens(tokens):
        return "".join(TOKEN_TO_STR[token] for token in tokens)
