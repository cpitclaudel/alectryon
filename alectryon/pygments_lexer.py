# Original implementation Copyright 2006-2019 by the Pygments team.
# Modifications Copyright © 2019 Clément Pit-Claudel.
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# * Redistributions of source code must retain the above copyright
#   notice, this list of conditions and the following disclaimer.
#
# * Redistributions in binary form must reproduce the above copyright
#   notice, this list of conditions and the following disclaimer in the
#   documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""
A custom Coq lexer for pygments.

Rewritten from the one in pygments.lexers.theorem.
"""

from pygments.lexer import RegexLexer, default, words, bygroups, include
from pygments.regexopt import regex_opt, regex_opt_inner
from pygments.token import Text, Comment, Operator, Keyword, Name, String, \
    Number, Punctuation, Generic

class CoqLexer(RegexLexer):
    """
    For the `Coq <http://coq.inria.fr/>`_ theorem prover.

    .. versionadded:: 1.5
    """

    name = 'Coq'
    aliases = ['coq']
    filenames = ['*.v']
    mimetypes = ['text/x-coq']

    kwds = {
        'cmd': ['Abort All', 'About', 'Add', 'Add LoadPath', 'Add ML Path',
                'Add Rec LoadPath', 'Add Rec ML Path', 'Add Relation',
                'Add Setoid', 'Admit Obligations', 'Admitted', 'Arguments',
                'As', 'Back', 'BackTo', 'Backtrack', 'Bind Scope', 'Cd',
                'Check', 'Close Scope', 'Compute', 'Create HintDb',
                'Cumulative', 'Declare Custom Entry', 'Declare Instance',
                'Declare Left Step', 'Declare ML Module', 'Declare Reduction',
                'Declare Right Step', 'Declare Scope', 'Defined',
                'Delimit Scope', 'Drop', 'Eval', 'Existential', 'Export',
                'Export Set', 'Export Unset', 'Extract Constant',
                'Extract Inductive', 'Extract Inlined Constant', 'Extraction',
                'Extraction Blacklist', 'Extraction Implicit',
                'Extraction Inline', 'Extraction Language Haskell',
                'Extraction Language OCaml', 'Extraction Language Scheme',
                'Extraction Library', 'Extraction NoInline',
                'Extraction TestCompile', 'Fail', 'Focus', 'From',
                'Generalizable All Variables', 'Generalizable No Variables',
                'Global', 'Global Arguments', 'Global Close Scope',
                'Global Generalizable', 'Global Instance',
                'Global Obligation Tactic', 'Global Opaque',
                'Global Open Scope', 'Global Set', 'Global Transparent',
                'Global Unset', 'Goal', 'Grab Existential Variables', 'Guarded',
                'Hint', 'Hint Constants Opaque', 'Hint Constants Transparent',
                'Hint Constructors', 'Hint Cut', 'Hint Extern',
                'Hint Immediate', 'Hint Mode', 'Hint Opaque', 'Hint Resolve',
                'Hint Rewrite', 'Hint Transparent', 'Hint Unfold',
                'Hint Variables Opaque', 'Hint Variables Transparent',
                'Hint View for apply', 'Hint View for move', 'Immediate',
                'Import', 'Include', 'Induction for', 'Infix', 'Info', 'Inline',
                'Inspect', 'Load', 'Load Verbose', 'Local', 'Local Arguments',
                'Local Axiom', 'Local Axioms', 'Local Close Scope',
                'Local Coercion', 'Local Conjecture', 'Local Conjectures',
                'Local Declare Custom Entry', 'Local Declare ML Module',
                'Local Definition', 'Local Example', 'Local Hint',
                'Local Identity Coercion', 'Local Ltac', 'Local Notation',
                'Local Obligation Tactic', 'Local Open Scope',
                'Local Parameter', 'Local Parameters', 'Local Set',
                'Local Strategy', 'Local SubClass', 'Local Tactic Notation',
                'Local Unset', 'Locate', 'Locate File', 'Locate Library',
                'Locate Ltac', 'Locate Module', 'Locate Term', 'Ltac2',
                'Ltac2 Eval', 'Ltac2 Notation', 'Ltac2 Set', 'Ltac2 Type',
                'Ltac2 Type rec', 'Ltac2 mutable', 'Ltac2 mutable rec',
                'Ltac2 rec', 'Minimality for', 'Module Export', 'Module Import',
                'Monomorphic', 'Next Obligation', 'NonCumulative',
                'Obligation Tactic', 'Obligation num', 'Obligations', 'Opaque',
                'Open Scope', 'Optimize Heap', 'Optimize Proof', 'Polymorphic',
                'Preterm', 'Print', 'Print All', 'Print All Dependencies',
                'Print Assumptions', 'Print Canonical Projections',
                'Print Classes', 'Print Coercion Paths', 'Print Coercions',
                'Print Extraction Blacklist', 'Print Extraction Inline',
                'Print Firstorder Solver', 'Print Grammar',
                'Print Grammar constr', 'Print Grammar pattern',
                'Print Grammar tactic', 'Print Graph', 'Print Hint',
                'Print HintDb', 'Print Implicit', 'Print Instances',
                'Print Libraries', 'Print LoadPath', 'Print Ltac',
                'Print Ltac Signatures', 'Print ML Modules', 'Print ML Path',
                'Print Module', 'Print Module Type',
                'Print Opaque Dependencies', 'Print Options',
                'Print Rewrite HintDb', 'Print Scope', 'Print Scopes',
                'Print Section', 'Print Sorted Universes', 'Print Strategies',
                'Print Strategy', 'Print Table', 'Print Tables', 'Print Term',
                'Print Transparent Dependencies', 'Print Universes',
                'Print Universes Subgraph', 'Print Visibility',
                'Program Definition', 'Program Fixpoint', 'Program Instance',
                'Program Lemma', 'Proof', 'Proof using All', 'Proof using Type',
                'Proof with', 'Pwd', 'Qed', 'Quit', 'Recursive Extraction',
                'Recursive Extraction Library', 'Redirect', 'Register',
                'Register Inline', 'Remove', 'Remove Hints', 'Remove LoadPath',
                'Require', 'Require Export', 'Require Import',
                'Reset Extraction Blacklist', 'Reset Extraction Inline',
                'Reset Initial', 'Reset Ltac Profile', 'Resolve', 'Restart',
                'Search', 'Search in', 'SearchAbout', 'SearchHead',
                'SearchPattern', 'SearchRewrite', 'Separate Extraction', 'Show',
                'Show Conjectures', 'Show Existentials', 'Show Intro',
                'Show Intros', 'Show Ltac Profile', 'Show Match',
                'Show Obligation Tactic', 'Show Proof', 'Show Script',
                'Show Universes', 'Solve All Obligations',
                'Solve All Obligations with', 'Solve Obligations',
                'Solve Obligations with', 'Sort', 'Strategy', 'SuchThat',
                'Tactic Notation', 'Test', 'Time', 'Timeout', 'Transparent',
                'Typeclasses Opaque', 'Typeclasses Transparent',
                'Typeclasses eauto', 'Undelimit Scope', 'Undo', 'Unfocus',
                'Unfocused', 'Unset', 'Unshelve', 'abstract after', 'and',
                'as ident', 'as pattern', 'as strict pattern', 'at level',
                'at next level', 'bfs', 'bigint', 'binder', 'clear implicits',
                'clear scopes', 'closed binder', 'constr at level',
                'constr at next level', 'custom', 'custom at level',
                'custom at next level', 'debug', 'default implicits', 'dfs',
                'discriminated', 'extra scopes', 'format', 'from', 'global',
                'ident', 'in custom', 'inside', 'left associativity', 'measure',
                'no associativity', 'only parsing', 'only printing', 'outside',
                'pattern at level', 'right associativity', 'strict pattern',
                'strict pattern at level', 'using tactic', 'warning after',
                'wf', 'where', 'with Induction for', 'with signature'],
        'decls': ['Class', 'CoFixpoint', 'CoInductive', 'Corollary',
                  'Definition', 'Example', 'Fact', 'Fixpoint', 'Inductive',
                  'Instance', 'Lemma', 'Let', 'Proposition', 'Record', 'Remark',
                  'Structure', 'Theorem', 'Variant'],
        'expects_binders': ['Add Parametric Morphism', 'Axiom', 'Axioms',
                            'Conjecture', 'Conjectures', 'Context',
                            'Hypotheses', 'Hypothesis', 'Implicit Types',
                            'Parameter', 'Parameters', 'Variable',
                            'Variables'],
        'expects_name': ['Abort', 'Add Field', 'Add Morphism', 'Add Ring',
                         'Admit Obligations of', 'Canonical',
                         'Canonical Structure', 'Coercion', 'Collection',
                         'Combined Scheme', 'Constraint', 'Declare Module',
                         'Derive', 'Derive Dependent Inversion',
                         'Derive Dependent Inversion_clear', 'Derive Inversion',
                         'Derive Inversion_clear', 'End', 'Existing Class',
                         'Existing Instance', 'Function', 'Functional Scheme',
                         'Generalizable Variable', 'Generalizable Variables',
                         'Identity Coercion', 'Implicit Type', 'Let CoFixpoint',
                         'Let Fixpoint', 'Ltac', 'Module', 'Module Type',
                         'Next Obligation of', 'Notation', 'Numeral Notation',
                         'Obligation num of', 'Obligations of',
                         'Prenex Implicits', 'Preterm of', 'Primitive',
                         'Proof using', 'Proof with tactic using', 'Reset',
                         'Save', 'Scheme', 'Scheme Equality for',
                         'Scheme Induction for', 'Section',
                         'Solve Obligations of', 'String Notation', 'SubClass',
                         'Universe'],
        'flag': ['Allow StrictProp', 'Asymmetric Patterns',
                 'Auto Template Polymorphism', 'Boolean Equality Schemes',
                 'Bracketing Last Introduction Pattern',
                 'Case Analysis Schemes', 'Congruence Verbose',
                 'Contextual Implicit', 'Coqtop Exit On Error',
                 'Cumulativity Weak Constraints', 'Debug Auto', 'Debug Cbv',
                 'Debug Eauto', 'Debug RAKAM', 'Debug SsrMatching',
                 'Debug Ssreflect', 'Debug Tactic Unification', 'Debug Trivial',
                 'Debug Unification', 'Decidable Equality Schemes',
                 'Elaboration StrictProp Cumulativity', 'Elimination Schemes',
                 'Extraction AutoInline', 'Extraction Conservative Types',
                 'Extraction KeepSingleton', 'Extraction Optimize',
                 'Extraction SafeImplicits', 'Extraction TypeExpand',
                 'Fast Name Printing', 'Hide Obligations', 'Implicit Arguments',
                 'Info Auto', 'Info Eauto', 'Info Trivial',
                 'Intuition Negation Unfolding', 'Keep Proof Equalities',
                 'Keyed Unification', 'Ltac Backtrace', 'Ltac Batch Debug',
                 'Ltac Debug', 'Ltac Profiling', 'Ltac2 Backtrace',
                 'Mangle Names', 'Maximal Implicit Insertion',
                 'NativeCompute Profiling', 'Nested Proofs Allowed',
                 'Nonrecursive Elimination Schemes', 'Omega Action',
                 'Omega System', 'Omega UseLocalDefs', 'Parsing Explicit',
                 'Polymorphic Inductive Cumulativity', 'Primitive Projections',
                 'Printing All', 'Printing Allow Match Default Clause',
                 'Printing Coercions', 'Printing Compact Contexts',
                 'Printing Dependent Evars Line',
                 'Printing Existential Instances',
                 'Printing Factorizable Match Patterns', 'Printing Implicit',
                 'Printing Implicit Defensive', 'Printing Matching',
                 'Printing Notations',
                 'Printing Primitive Projection Parameters',
                 'Printing Projections', 'Printing Records', 'Printing Synth',
                 'Printing Unfocused', 'Printing Universes',
                 'Printing Wildcard', 'Private Polymorphic Universes',
                 'Program Cases', 'Program Generalized Coercion',
                 'Program Mode', 'Refine Instance Mode', 'Regular Subst Tactic',
                 'Reversible Pattern Implicit', 'Rewriting Schemes',
                 'Search Output Name Only', 'Short Module Printing',
                 'Shrink Obligations', 'Silent', 'Simplex',
                 'Solve Unification Constraints', 'SsrHave NoTCResolution',
                 'SsrIdents', 'SsrOldRewriteGoalsOrder', 'SsrRewrite',
                 'Stable Omega', 'Strict Implicit',
                 'Strict Universe Declaration', 'Strongly Strict Implicit',
                 'Structural Injection', 'Suggest Proof Using',
                 'Transparent Obligations',
                 'Typeclass Resolution For Conversion', 'Typeclasses Debug',
                 'Typeclasses Dependency Order',
                 'Typeclasses Filtered Unification',
                 'Typeclasses Iterative Deepening', 'Typeclasses Limit Intros',
                 'Typeclasses Strict Resolution',
                 'Typeclasses Unique Instances', 'Typeclasses Unique Solutions',
                 'Uniform Inductive Parameters',
                 'Universal Lemma Under Conjunction',
                 'Universe Minimization ToSet', 'Universe Polymorphism'],
        'gallina-constants': ['False', 'Funclass', 'Prop', 'SProp', 'Set',
                              'Sortclass', 'True', 'Type'],
        'gallina-keywords': ['as', 'cofix', 'else', 'end', 'exists', 'exists2',
                             'fix', 'for', 'forall', 'fun', 'if', 'in', 'is',
                             "isn't", 'let', 'let cofix', 'let fix', 'ltac2',
                             'match', 'return', 'struct', 'then', 'with'],
        'ltac-builtins': ['all', 'assert_fails', 'assert_succeeds', 'constr',
                          'context', 'do', 'eval', 'exactly_once', 'fail',
                          'first', 'fresh', 'guard', 'idtac', 'ltac',
                          'numgoals', 'once', 'only', 'par', 'progress',
                          'repeat', 'solve', 'time', 'timeout', 'try', 'tryif',
                          'type of', 'type_term', 'uconstr', 'using'],
        'ltac-keywords': ['lazy_match!', 'lazy_match! goal with',
                          'lazy_match! reverse goal with', 'lazymatch',
                          'lazymatch goal with', 'lazymatch reverse goal with',
                          'let rec', 'match goal with',
                          'match reverse goal with', 'match!',
                          'match! goal with', 'match! reverse goal with',
                          'multi_match!', 'multi_match! goal with',
                          'multi_match! reverse goal with', 'multimatch',
                          'multimatch goal with',
                          'multimatch reverse goal with'],
        'opt': ['Bullet Behavior "None"', 'Bullet Behavior "Strict Subproofs"',
                'Default Goal Selector', 'Default Proof Using',
                'Default Timeout', 'Diffs "off"', 'Diffs "on"',
                'Diffs "removed"', 'Extraction File Comment', 'Extraction Flag',
                'Firstorder Depth', 'Firstorder Solver', 'Hyps Limit',
                'Info Level', 'Loose Hint Behavior "Lax"',
                'Loose Hint Behavior "Strict"', 'Loose Hint Behavior "Warn"',
                'Mangle Names Prefix', 'NativeCompute Profile Filename',
                'Printing Depth', 'Printing Width',
                'Typeclasses Debug Verbosity', 'Typeclasses Depth',
                'Warnings'],
        'table': ['Printing Coercion', 'Printing Constructor', 'Printing If',
                  'Printing Let', 'Printing Record', 'Search Blacklist'],
        'tacn': ['abstract', 'absurd', 'admit', 'after', 'apply', 'assert',
                 'assumption', 'at', 'at bottom', 'at occurrences', 'at top',
                 'auto', 'auto using', 'auto with', 'autoapply',
                 'autorewrite with', 'autounfold with', 'before', 'btauto',
                 'by', 'by rewrite over', 'by tactic', 'case', 'case_eq', 'cbn',
                 'cbv', 'change', 'change_no_check', 'classical_left',
                 'classical_right', 'clear', 'clear dependent', 'clearbody',
                 'compare', 'compute', 'congr', 'congruence', 'congruence n',
                 'congruence with', 'constr_eq', 'constr_eq_strict',
                 'constructor', 'contradict', 'contradiction', 'conv_tactic in',
                 'convert_concl_no_check', 'cut', 'cutrewrite', 'cycle',
                 'd_item', 'debug auto', 'debug trivial', 'decide equality',
                 'decompose', 'decompose record', 'decompose sum',
                 'dependent destruction', 'dependent induction',
                 'dependent inversion', 'dependent inversion_clear',
                 'dependent rewrite', 'destruct', 'dintuition', 'discrR',
                 'discriminate', 'done', 'double induction', 'dtauto', 'eapply',
                 'eassert', 'eassumption', 'easy', 'eauto', 'eauto using',
                 'eauto with', 'ecase', 'econstructor', 'edestruct',
                 'ediscriminate', 'eelim', 'eenough', 'eexact', 'eexists',
                 'einduction', 'einjection', 'einjection as', 'eintros',
                 'eleft', 'elim', 'elimtype', 'enough', 'epose', 'epose proof',
                 'eqn', 'eremember', 'erewrite', 'eright', 'eset',
                 'esimplify_eq', 'esplit', 'evar', 'exact', 'exact_no_check',
                 'exfalso', 'f_equal', 'fail message_token', 'field',
                 'field_simplify', 'field_simplify in', 'field_simplify_eq',
                 'field_simplify_eq in', 'finish_timing', 'first last',
                 'firstorder', 'firstorder tactic using', 'firstorder using',
                 'firstorder with', 'fold', 'fresh component',
                 'function induction', 'functional induction',
                 'functional inversion', 'gen have', 'generalize',
                 'generalize dependent', 'generalizing', 'generally have',
                 'gfail', 'gfail message_token', 'give_up', 'has_evar', 'have',
                 'have suff', 'hnf', 'in clause', 'in clause by', 'induction',
                 'info_auto', 'info_auto using', 'info_auto with', 'info_eauto',
                 'info_eauto using', 'info_eauto with', 'info_trivial',
                 'info_trivial using', 'info_trivial with', 'injection',
                 'injection as', 'instantiate', 'into', 'intro', 'intro after',
                 'intro at bottom', 'intro at top', 'intro before', 'intros',
                 'intros until', 'intuition', 'inversion', 'inversion_clear',
                 'inversion_sigma', 'is_evar', 'is_var', 'lapply', 'last',
                 'last first', 'lazy', 'left', 'left with', 'lia', 'lra',
                 'message_token', 'move', 'native_cast_no_check',
                 'native_compute', 'nia', 'notypeclasses refine', 'now',
                 'now_show', 'nra', 'nsatz', 'nsatz with radicalmax', 'omega',
                 'optimize_heap', 'over', 'parameters', 'pattern', 'pose',
                 'pose cofix', 'pose fix', 'pose proof', 'psatz', 'red',
                 'refine', 'reflexivity', 'remember', 'rename', 'replace',
                 'reset ltac profile', 'restart_timer', 'revert',
                 'revert dependent', 'revgoals', 'rewrite', 'rewrite_strat',
                 'right', 'right with', 'ring', 'ring_simplify', 'rtauto',
                 'set', 'setoid_reflexivity', 'setoid_replace',
                 'setoid_rewrite', 'setoid_symmetry', 'setoid_symmetry in',
                 'setoid_transitivity', 'shelve', 'shelve_unifiable',
                 'show ltac profile', 'simpl', 'simple apply',
                 'simple destruct', 'simple eapply', 'simple induction',
                 'simple inversion', 'simple notypeclasses refine',
                 'simple refine', 'simplify_eq', 'solve_constraints',
                 'specialize', 'split', 'split with', 'split_Rabs',
                 'split_Rmult', 'start ltac profiling', 'stepl', 'stepr',
                 'stop ltac profiling', 'strategy', 'subst', 'suff',
                 'suff have', 'suffices', 'suffices have', 'swap', 'symmetry',
                 'symmetry in', 'tauto', 'time_constr', 'transitivity',
                 'transparent_abstract', 'trivial', 'trivial using',
                 'trivial with', 'typeclasses eauto', 'typeclasses eauto with',
                 'under', 'unfold', 'unfold qualid_or_string at', 'unify',
                 'unlock', 'unshelve', 'using relation', 'value of',
                 'variables', 'vm_cast_no_check', 'vm_compute', 'without loss',
                 'without loss suff', 'wlog', 'wlog suff']
    }

    # This is auto-generated from Coq's source code
    identstart = ('\x41-\x5A\x5F\x61-\x7A'
                  '\xA0\xAA\xB5'
                  '\xBA\xC0-\xD6\xD8-\xF6'
                  '\xF8-\u02C1\u02C6-\u02D1\u02E0-\u02E4'
                  '\u02EC\u02EE\u0370-\u0374'
                  '\u0376-\u0377\u037A-\u037D\u037F'
                  '\u0386\u0388-\u038A\u038C'
                  '\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481'
                  '\u048A-\u052F\u0531-\u0556\u0559'
                  '\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2'
                  '\u0620-\u064A\u066E-\u066F\u0671-\u06D3'
                  '\u06D5\u06E5-\u06E6\u06EE-\u06EF'
                  '\u06FA-\u06FC\u06FF\u0710'
                  '\u0712-\u072F\u074D-\u07A5\u07B1'
                  '\u07CA-\u07EA\u07F4-\u07F5\u07FA'
                  '\u0800-\u0815\u081A\u0824'
                  '\u0828\u0840-\u0858\u08A0-\u08B4'
                  '\u08B6-\u08BD\u0904-\u0939\u093D'
                  '\u0950\u0958-\u0961\u0971-\u0980'
                  '\u0985-\u098C\u098F-\u0990\u0993-\u09A8'
                  '\u09AA-\u09B0\u09B2\u09B6-\u09B9'
                  '\u09BD\u09CE\u09DC-\u09DD'
                  '\u09DF-\u09E1\u09F0-\u09F1\u0A05-\u0A0A'
                  '\u0A0F-\u0A10\u0A13-\u0A28\u0A2A-\u0A30'
                  '\u0A32-\u0A33\u0A35-\u0A36\u0A38-\u0A39'
                  '\u0A59-\u0A5C\u0A5E\u0A72-\u0A74'
                  '\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8'
                  '\u0AAA-\u0AB0\u0AB2-\u0AB3\u0AB5-\u0AB9'
                  '\u0ABD\u0AD0\u0AE0-\u0AE1'
                  '\u0AF9\u0B05-\u0B0C\u0B0F-\u0B10'
                  '\u0B13-\u0B28\u0B2A-\u0B30\u0B32-\u0B33'
                  '\u0B35-\u0B39\u0B3D\u0B5C-\u0B5D'
                  '\u0B5F-\u0B61\u0B71\u0B83'
                  '\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95'
                  '\u0B99-\u0B9A\u0B9C\u0B9E-\u0B9F'
                  '\u0BA3-\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9'
                  '\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10'
                  '\u0C12-\u0C28\u0C2A-\u0C39\u0C3D'
                  '\u0C58-\u0C5A\u0C60-\u0C61\u0C80'
                  '\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8'
                  '\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD'
                  '\u0CDE\u0CE0-\u0CE1\u0CF1-\u0CF2'
                  '\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A'
                  '\u0D3D\u0D4E\u0D54-\u0D56'
                  '\u0D5F-\u0D61\u0D7A-\u0D7F\u0D85-\u0D96'
                  '\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD'
                  '\u0DC0-\u0DC6\u0E01-\u0E30\u0E32-\u0E33'
                  '\u0E40-\u0E46\u0E81-\u0E82\u0E84'
                  '\u0E87-\u0E88\u0E8A\u0E8D'
                  '\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3'
                  '\u0EA5\u0EA7\u0EAA-\u0EAB'
                  '\u0EAD-\u0EB0\u0EB2-\u0EB3\u0EBD'
                  '\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF'
                  '\u0F00\u0F40-\u0F47\u0F49-\u0F6C'
                  '\u0F88-\u0F8C\u1000-\u102A\u103F'
                  '\u1050-\u1055\u105A-\u105D\u1061'
                  '\u1065-\u1066\u106E-\u1070\u1075-\u1081'
                  '\u108E\u10A0-\u10C5\u10C7'
                  '\u10CD\u10D0-\u10FA\u10FC-\u1248'
                  '\u124A-\u124D\u1250-\u1256\u1258'
                  '\u125A-\u125D\u1260-\u1288\u128A-\u128D'
                  '\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE'
                  '\u12C0\u12C2-\u12C5\u12C8-\u12D6'
                  '\u12D8-\u1310\u1312-\u1315\u1318-\u135A'
                  '\u1380-\u138F\u13A0-\u13F5\u13F8-\u13FD'
                  '\u1401-\u166C\u166F-\u167F\u1681-\u169A'
                  '\u16A0-\u16EA\u16F1-\u16F8\u1700-\u170C'
                  '\u170E-\u1711\u1720-\u1731\u1740-\u1751'
                  '\u1760-\u176C\u176E-\u1770\u1780-\u17B3'
                  '\u17D7\u17DC\u1820-\u1877'
                  '\u1880-\u1884\u1887-\u18A8\u18AA'
                  '\u18B0-\u18F5\u1900-\u191E\u1950-\u196D'
                  '\u1970-\u1974\u1980-\u19AB\u19B0-\u19C9'
                  '\u1A00-\u1A16\u1A20-\u1A54\u1AA7'
                  '\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0'
                  '\u1BAE-\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23'
                  '\u1C4D-\u1C4F\u1C5A-\u1C7D\u1C80-\u1C88'
                  '\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5-\u1CF6'
                  '\u1D00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45'
                  '\u1F48-\u1F4D\u1F50-\u1F57\u1F59'
                  '\u1F5B\u1F5D\u1F5F-\u1F7D'
                  '\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE'
                  '\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3'
                  '\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4'
                  '\u1FF6-\u1FFB\u2071\u207F'
                  '\u2090-\u209C\u2102\u2107'
                  '\u210A-\u2113\u2115\u2119-\u211D'
                  '\u2124\u2126\u2128'
                  '\u212A-\u212D\u212F-\u2139\u213C-\u213F'
                  '\u2145-\u2149\u214E\u2183-\u2184'
                  '\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4'
                  '\u2CEB-\u2CEE\u2CF2-\u2CF3\u2D00-\u2D25'
                  '\u2D27\u2D2D\u2D30-\u2D67'
                  '\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6'
                  '\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE'
                  '\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6'
                  '\u2DD8-\u2DDE\u2E2F\u3005-\u3006'
                  '\u3031-\u3035\u303B-\u303C\u3041-\u3096'
                  '\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF'
                  '\u3105-\u312D\u3131-\u318E\u31A0-\u31BA'
                  '\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FD5'
                  '\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C'
                  '\uA610-\uA61F\uA62A-\uA62B\uA640-\uA66E'
                  '\uA67F-\uA69D\uA6A0-\uA6E5\uA717-\uA71F'
                  '\uA722-\uA788\uA78B-\uA7AE\uA7B0-\uA7B7'
                  '\uA7F7-\uA801\uA803-\uA805\uA807-\uA80A'
                  '\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3'
                  '\uA8F2-\uA8F7\uA8FB\uA8FD'
                  '\uA90A-\uA925\uA930-\uA946\uA960-\uA97C'
                  '\uA984-\uA9B2\uA9CF\uA9E0-\uA9E4'
                  '\uA9E6-\uA9EF\uA9FA-\uA9FE\uAA00-\uAA28'
                  '\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76'
                  '\uAA7A\uAA7E-\uAAAF\uAAB1'
                  '\uAAB5-\uAAB6\uAAB9-\uAABD\uAAC0'
                  '\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA'
                  '\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E'
                  '\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E'
                  '\uAB30-\uAB5A\uAB5C-\uAB65\uAB70-\uABE2'
                  '\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB'
                  '\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06'
                  '\uFB13-\uFB17\uFB1D\uFB1F-\uFB28'
                  '\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E'
                  '\uFB40-\uFB41\uFB43-\uFB44\uFB46-\uFBB1'
                  '\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7'
                  '\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC'
                  '\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE'
                  '\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7'
                  '\uFFDA-\uFFDC\U00010000-\U0001000B\U0001000D-\U00010026'
                  '\U00010028-\U0001003A\U0001003C-\U0001003D\U0001003F-\U0001004D'
                  '\U00010050-\U0001005D\U00010080-\U000100FA\U00010280-\U0001029C'
                  '\U000102A0-\U000102D0\U00010300-\U0001031F\U00010330-\U00010340'
                  '\U00010342-\U00010349\U00010350-\U00010375\U00010380-\U0001039D'
                  '\U000103A0-\U000103C3\U000103C8-\U000103CF\U00010400-\U0001049D'
                  '\U000104B0-\U000104D3\U000104D8-\U000104FB\U00010500-\U00010527'
                  '\U00010530-\U00010563\U00010600-\U00010736\U00010740-\U00010755'
                  '\U00010760-\U00010767\U00010800-\U00010805\U00010808'
                  '\U0001080A-\U00010835\U00010837-\U00010838\U0001083C'
                  '\U0001083F-\U00010855\U00010860-\U00010876\U00010880-\U0001089E'
                  '\U000108E0-\U000108F2\U000108F4-\U000108F5\U00010900-\U00010915'
                  '\U00010920-\U00010939\U00010980-\U000109B7\U000109BE-\U000109BF'
                  '\U00010A00\U00010A10-\U00010A13\U00010A15-\U00010A17'
                  '\U00010A19-\U00010A33\U00010A60-\U00010A7C\U00010A80-\U00010A9C'
                  '\U00010AC0-\U00010AC7\U00010AC9-\U00010AE4\U00010B00-\U00010B35'
                  '\U00010B40-\U00010B55\U00010B60-\U00010B72\U00010B80-\U00010B91'
                  '\U00010C00-\U00010C48\U00010C80-\U00010CB2\U00010CC0-\U00010CF2'
                  '\U00011003-\U00011037\U00011083-\U000110AF\U000110D0-\U000110E8'
                  '\U00011103-\U00011126\U00011150-\U00011172\U00011176'
                  '\U00011183-\U000111B2\U000111C1-\U000111C4\U000111DA'
                  '\U000111DC\U00011200-\U00011211\U00011213-\U0001122B'
                  '\U00011280-\U00011286\U00011288\U0001128A-\U0001128D'
                  '\U0001128F-\U0001129D\U0001129F-\U000112A8\U000112B0-\U000112DE'
                  '\U00011305-\U0001130C\U0001130F-\U00011310\U00011313-\U00011328'
                  '\U0001132A-\U00011330\U00011332-\U00011333\U00011335-\U00011339'
                  '\U0001133D\U00011350\U0001135D-\U00011361'
                  '\U00011400-\U00011434\U00011447-\U0001144A\U00011480-\U000114AF'
                  '\U000114C4-\U000114C5\U000114C7\U00011580-\U000115AE'
                  '\U000115D8-\U000115DB\U00011600-\U0001162F\U00011644'
                  '\U00011680-\U000116AA\U00011700-\U00011719\U000118A0-\U000118DF'
                  '\U000118FF\U00011AC0-\U00011AF8\U00011C00-\U00011C08'
                  '\U00011C0A-\U00011C2E\U00011C40\U00011C72-\U00011C8F'
                  '\U00012000-\U00012399\U00012480-\U00012543\U00013000-\U0001342E'
                  '\U00014400-\U00014646\U00016800-\U00016A38\U00016A40-\U00016A5E'
                  '\U00016AD0-\U00016AED\U00016B00-\U00016B2F\U00016B40-\U00016B43'
                  '\U00016B63-\U00016B77\U00016B7D-\U00016B8F\U00016F00-\U00016F44'
                  '\U00016F50\U00016F93-\U00016F9F\U00017000-\U000187EC'
                  '\U00018800-\U00018AF2\U0001B000-\U0001B001\U0001BC00-\U0001BC6A'
                  '\U0001BC70-\U0001BC7C\U0001BC80-\U0001BC88\U0001BC90-\U0001BC99'
                  '\U0001D400-\U0001D454\U0001D456-\U0001D49C\U0001D49E-\U0001D49F'
                  '\U0001D4A2\U0001D4A5-\U0001D4A6\U0001D4A9-\U0001D4AC'
                  '\U0001D4AE-\U0001D4B9\U0001D4BB\U0001D4BD-\U0001D4C3'
                  '\U0001D4C5-\U0001D505\U0001D507-\U0001D50A\U0001D50D-\U0001D514'
                  '\U0001D516-\U0001D51C\U0001D51E-\U0001D539\U0001D53B-\U0001D53E'
                  '\U0001D540-\U0001D544\U0001D546\U0001D54A-\U0001D550'
                  '\U0001D552-\U0001D6A5\U0001D6A8-\U0001D6C0\U0001D6C2-\U0001D6DA'
                  '\U0001D6DC-\U0001D6FA\U0001D6FC-\U0001D714\U0001D716-\U0001D734'
                  '\U0001D736-\U0001D74E\U0001D750-\U0001D76E\U0001D770-\U0001D788'
                  '\U0001D78A-\U0001D7A8\U0001D7AA-\U0001D7C2\U0001D7C4-\U0001D7CB'
                  '\U0001E800-\U0001E8C4\U0001EE00-\U0001EE03\U0001EE05-\U0001EE1F'
                  '\U0001EE21-\U0001EE22\U0001EE24\U0001EE27'
                  '\U0001EE29-\U0001EE32\U0001EE34-\U0001EE37\U0001EE39'
                  '\U0001EE3B\U0001EE42\U0001EE47'
                  '\U0001EE49\U0001EE4B\U0001EE4D-\U0001EE4F'
                  '\U0001EE51-\U0001EE52\U0001EE54\U0001EE57'
                  '\U0001EE59\U0001EE5B\U0001EE5D'
                  '\U0001EE5F\U0001EE61-\U0001EE62\U0001EE64'
                  '\U0001EE67-\U0001EE6A\U0001EE6C-\U0001EE72\U0001EE74-\U0001EE77'
                  '\U0001EE79-\U0001EE7C\U0001EE7E\U0001EE80-\U0001EE89'
                  '\U0001EE8B-\U0001EE9B\U0001EEA1-\U0001EEA3\U0001EEA5-\U0001EEA9'
                  '\U0001EEAB-\U0001EEBB\U00020000-\U0002A6D6\U0002A700-\U0002B734'
                  '\U0002B740-\U0002B81D\U0002B820-\U0002CEA1')
    identpart = (identstart + '\x27\x30-\x39\xB2-\xB3'
                 '\xB9\xBC-\xBE\u0660-\u0669'
                 '\u06F0-\u06F9\u07C0-\u07C9\u0966-\u096F'
                 '\u09E6-\u09EF\u09F4-\u09F9\u0A66-\u0A6F'
                 '\u0AE6-\u0AEF\u0B66-\u0B6F\u0B72-\u0B77'
                 '\u0BE6-\u0BF2\u0C66-\u0C6F\u0C78-\u0C7E'
                 '\u0CE6-\u0CEF\u0D58-\u0D5E\u0D66-\u0D78'
                 '\u0DE6-\u0DEF\u0E50-\u0E59\u0ED0-\u0ED9'
                 '\u0F20-\u0F33\u1040-\u1049\u1090-\u1099'
                 '\u1369-\u137C\u16EE-\u16F0\u17E0-\u17E9'
                 '\u17F0-\u17F9\u1810-\u1819\u1946-\u194F'
                 '\u19D0-\u19DA\u1A80-\u1A89\u1A90-\u1A99'
                 '\u1B50-\u1B59\u1BB0-\u1BB9\u1C40-\u1C49'
                 '\u1C50-\u1C59\u2070\u2074-\u2079'
                 '\u2080-\u2089\u2150-\u2182\u2185-\u2189'
                 '\u2460-\u249B\u24EA-\u24FF\u2776-\u2793'
                 '\u2CFD\u3007\u3021-\u3029'
                 '\u3038-\u303A\u3192-\u3195\u3220-\u3229'
                 '\u3248-\u324F\u3251-\u325F\u3280-\u3289'
                 '\u32B1-\u32BF\uA620-\uA629\uA6E6-\uA6EF'
                 '\uA830-\uA835\uA8D0-\uA8D9\uA900-\uA909'
                 '\uA9D0-\uA9D9\uA9F0-\uA9F9\uAA50-\uAA59'
                 '\uABF0-\uABF9\uFF10-\uFF19\U00010107-\U00010133'
                 '\U00010140-\U00010178\U0001018A-\U0001018B\U000102E1-\U000102FB'
                 '\U00010320-\U00010323\U00010341\U0001034A'
                 '\U000103D1-\U000103D5\U000104A0-\U000104A9\U00010858-\U0001085F'
                 '\U00010879-\U0001087F\U000108A7-\U000108AF\U000108FB-\U000108FF'
                 '\U00010916-\U0001091B\U000109BC-\U000109BD\U000109C0-\U000109CF'
                 '\U000109D2-\U000109FF\U00010A40-\U00010A47\U00010A7D-\U00010A7E'
                 '\U00010A9D-\U00010A9F\U00010AEB-\U00010AEF\U00010B58-\U00010B5F'
                 '\U00010B78-\U00010B7F\U00010BA9-\U00010BAF\U00010CFA-\U00010CFF'
                 '\U00010E60-\U00010E7E\U00011052-\U0001106F\U000110F0-\U000110F9'
                 '\U00011136-\U0001113F\U000111D0-\U000111D9\U000111E1-\U000111F4'
                 '\U000112F0-\U000112F9\U00011450-\U00011459\U000114D0-\U000114D9'
                 '\U00011650-\U00011659\U000116C0-\U000116C9\U00011730-\U0001173B'
                 '\U000118E0-\U000118F2\U00011C50-\U00011C6C\U00016A60-\U00016A69'
                 '\U00016B50-\U00016B59\U00016B5B-\U00016B61\U0001D360-\U0001D371'
                 '\U0001D7CE-\U0001D7FF\U0001E8C7-\U0001E8CF')
    symbol = ('\x21-\x2F\x3A-\x40\x5B-\x60'
              '\x7B-\x7E\xA1-\xA9\xAB-\xAC'
              '\xAE-\xB4\xB6-\xB9\xBB'
              '\xBF\xD7\xF7'
              '\u02C2-\u02C5\u02D2-\u02DF\u02E5-\u02EB'
              '\u02ED\u02EF-\u02FF\u0375'
              '\u037E\u0384-\u0385\u0387'
              '\u03F6\u0482\u055A-\u055F'
              '\u0589-\u058A\u058D-\u058F\u05BE'
              '\u05C0\u05C3\u05C6'
              '\u05F3-\u05F4\u0606-\u060F\u061B'
              '\u061E-\u061F\u066A-\u066D\u06D4'
              '\u06DE\u06E9\u06FD-\u06FE'
              '\u0700-\u070D\u07F6-\u07F9\u0830-\u083E'
              '\u085E\u0964-\u0965\u0970'
              '\u09F2-\u09F3\u09FA-\u09FB\u0AF0-\u0AF1'
              '\u0B70\u0BF3-\u0BFA\u0C7F'
              '\u0D4F\u0D79\u0DF4'
              '\u0E3F\u0E4F\u0E5A-\u0E5B'
              '\u0F01-\u0F17\u0F1A-\u0F1F\u0F34'
              '\u0F36\u0F38\u0F3A-\u0F3D'
              '\u0F85\u0FBE-\u0FC5\u0FC7-\u0FCC'
              '\u0FCE-\u0FDA\u104A-\u104F\u109E-\u109F'
              '\u10FB\u1360-\u1368\u1390-\u1399'
              '\u1400\u166D-\u166E\u169B-\u169C'
              '\u16EB-\u16ED\u1735-\u1736\u17D4-\u17D6'
              '\u17D8-\u17DB\u1800-\u180A\u1940'
              '\u1944-\u1945\u19DE-\u19FF\u1A1E-\u1A1F'
              '\u1AA0-\u1AA6\u1AA8-\u1AAD\u1B5A-\u1B6A'
              '\u1B74-\u1B7C\u1BFC-\u1BFF\u1C3B-\u1C3F'
              '\u1C7E-\u1C7F\u1CC0-\u1CC7\u1CD3'
              '\u1FBD\u1FBF-\u1FC1\u1FCD-\u1FCF'
              '\u1FDD-\u1FDF\u1FED-\u1FEF\u1FFD-\u1FFE'
              '\u2010-\u2027\u2030-\u205E\u2070'
              '\u2074-\u207E\u208A-\u208E\u20A0-\u20BE'
              '\u2100-\u2101\u2103-\u2106\u2108-\u2109'
              '\u2114\u2116-\u2118\u211E-\u2123'
              '\u2125\u2127\u2129'
              '\u212E\u213A-\u213B\u2140-\u2144'
              '\u214A-\u214D\u214F\u218A-\u218B'
              '\u2190-\u23FE\u2400-\u2426\u2440-\u244A'
              '\u249C-\u24E9\u2500-\u2775\u2794-\u2B73'
              '\u2B76-\u2B95\u2B98-\u2BB9\u2BBD-\u2BC8'
              '\u2BCA-\u2BD1\u2BEC-\u2BEF\u2CE5-\u2CEA'
              '\u2CF9-\u2CFC\u2CFE-\u2CFF\u2D70'
              '\u2E00-\u2E1F\u2E22-\u2E2E\u2E30-\u2E44'
              '\u2E80-\u2E99\u2E9B-\u2EF3\u2F00-\u2FD5'
              '\u2FF0-\u2FFB\u3001-\u3004\u3008-\u3020'
              '\u3030\u3036-\u3037\u303D-\u303F'
              '\u309B-\u309C\u30A0\u30FB'
              '\u3190-\u3191\u3196-\u319F\u31C0-\u31E3'
              '\u3200-\u321E\u322A-\u3247\u3250'
              '\u3260-\u327F\u328A-\u32B0\u32C0-\u32FE'
              '\u3300-\u33FF\u4DC0-\u4DFF\uA490-\uA4C6'
              '\uA4FE-\uA4FF\uA60D-\uA60F\uA673'
              '\uA67E\uA6F2-\uA6F7\uA700-\uA716'
              '\uA720-\uA721\uA789-\uA78A\uA828-\uA82B'
              '\uA836-\uA839\uA874-\uA877\uA8CE-\uA8CF'
              '\uA8F8-\uA8FA\uA8FC\uA92E-\uA92F'
              '\uA95F\uA9C1-\uA9CD\uA9DE-\uA9DF'
              '\uAA5C-\uAA5F\uAA77-\uAA79\uAADE-\uAADF'
              '\uAAF0-\uAAF1\uAB5B\uABEB'
              '\uFB29\uFBB2-\uFBC1\uFD3E-\uFD3F'
              '\uFDFC-\uFDFD\uFE10-\uFE19\uFE30-\uFE52'
              '\uFE54-\uFE66\uFE68-\uFE6B\uFF01-\uFF0C'
              '\uFF0E-\uFF0F\uFF1A-\uFF20\uFF3B-\uFF3E'
              '\uFF40\uFF5B-\uFF61\uFF64-\uFF65'
              '\uFFE0-\uFFE4\uFFE8-\uFFEE\uFFFC-\uFFFD'
              '\U00010100-\U00010102\U00010137-\U0001013F\U00010179-\U00010189'
              '\U0001018C-\U0001018E\U00010190-\U0001019B\U000101A0'
              '\U000101D0-\U000101FC\U0001039F\U000103D0'
              '\U0001056F\U00010857\U00010877-\U00010878'
              '\U0001091F\U0001093F\U00010A50-\U00010A58'
              '\U00010A7F\U00010AC8\U00010AF0-\U00010AF6'
              '\U00010B39-\U00010B3F\U00010B99-\U00010B9C\U00011047-\U0001104D'
              '\U000110BB-\U000110BC\U000110BE-\U000110C1\U00011140-\U00011143'
              '\U00011174-\U00011175\U000111C5-\U000111C9\U000111CD'
              '\U000111DB\U000111DD-\U000111DF\U00011238-\U0001123D'
              '\U000112A9\U0001144B-\U0001144F\U0001145B'
              '\U0001145D\U000114C6\U000115C1-\U000115D7'
              '\U00011641-\U00011643\U00011660-\U0001166C\U0001173C-\U0001173F'
              '\U00011C41-\U00011C45\U00011C70-\U00011C71\U00012470-\U00012474'
              '\U00016A6E-\U00016A6F\U00016AF5\U00016B37-\U00016B3F'
              '\U00016B44-\U00016B45\U0001BC9C\U0001BC9F'
              '\U0001D000-\U0001D0F5\U0001D100-\U0001D126\U0001D129-\U0001D164'
              '\U0001D16A-\U0001D16C\U0001D183-\U0001D184\U0001D18C-\U0001D1A9'
              '\U0001D1AE-\U0001D1E8\U0001D200-\U0001D241\U0001D245'
              '\U0001D300-\U0001D356\U0001D6C1\U0001D6DB'
              '\U0001D6FB\U0001D715\U0001D735'
              '\U0001D74F\U0001D76F\U0001D789'
              '\U0001D7A9\U0001D7C3\U0001D800-\U0001D9FF'
              '\U0001DA37-\U0001DA3A\U0001DA6D-\U0001DA74\U0001DA76-\U0001DA83'
              '\U0001DA85-\U0001DA8B\U0001F000-\U0001F02B\U0001F030-\U0001F093'
              '\U0001F0A0-\U0001F0AE\U0001F0B1-\U0001F0BF\U0001F0C1-\U0001F0CF'
              '\U0001F0D1-\U0001F0F5\U0001F110-\U0001F12E\U0001F130-\U0001F16B'
              '\U0001F170-\U0001F1AC\U0001F1E6-\U0001F202\U0001F210-\U0001F23B'
              '\U0001F240-\U0001F248\U0001F250-\U0001F251\U0001F300-\U0001F3FA'
              '\U0001F400-\U0001F6D2\U0001F6E0-\U0001F6EC\U0001F6F0-\U0001F6F6'
              '\U0001F700-\U0001F773\U0001F780-\U0001F7D4\U0001F800-\U0001F80B'
              '\U0001F810-\U0001F847\U0001F850-\U0001F859\U0001F860-\U0001F887'
              '\U0001F890-\U0001F8AD\U0001F910-\U0001F91E\U0001F920-\U0001F927'
              '\U0001F930\U0001F933-\U0001F93E\U0001F940-\U0001F94B'
              '\U0001F950-\U0001F95E\U0001F980-\U0001F991')

    local_global = regex_opt_inner(("Local","Global","Export"), '(?:')
    set_unset_test = regex_opt_inner(("Set","Unset","Test"), '(?:')
    add_remove_test = regex_opt_inner(("Add","Remove","Test"), '(?:')

    opts = regex_opt(kwds['flag'] + kwds['opt'])
    opts_re = r"\b(?:{} )?(?:{} ){}\b".format(local_global, set_unset_test, opts)
    tables = regex_opt(kwds['table'])
    tables_re = r"\b(?:{} ){}\b".format(add_remove_test, tables)

    decls = regex_opt(kwds['decls'])
    decls_re = r"\b(?:{} )?(?:Program )?{}\b".format(local_global, decls)
    expects_name = regex_opt(kwds['expects_name'])
    expects_name_re = r"\b(?:{} )?{}\b".format(local_global, expects_name)
    expects_binders = regex_opt(kwds['expects_binders'])
    expects_binders_re = r"\b(?:{} )?{}\b".format(local_global, expects_binders)
    cmd = kwds['cmd'] + kwds['decls'] + kwds['expects_name'] + kwds['expects_binders']

    name_re = r"[{}][{}]*".format(identstart, identpart)

    ws = lambda w: words(w, prefix=r'\b', suffix=r'\b')

    comment = lambda token: [
        (r'[^(*)]+', token),
        (r'\(\*', token, '#push'),
        (r'\*\)', token, '#pop'),
        (r'[(*)]', token),
    ]
    binders = lambda regex, name_re: [
        (regex, Operator, '#pop'),
        (":", Operator, '#pop'),
        (name_re, Name.Variable),
        (r"\(", Operator, ('in parens', 'type annot')),
        include('_basic'),
        default('#pop'),
    ]

    # Names starting with '_' are not real states; they are just intended to be
    # included into other states.
    tokens = {
        'root': [
            include('_basic'),
            include('_vernac'),
            include('_keywords'),
            include('_other'),
        ],

        '_gallina': [
            include('_basic'),
            include('_keywords'),
            include('_other'),
        ],

        '_basic': [
            (r'\s+', Text),
            (r'\(\*\*\s', String.Doc, 'docstring'),
            (r'\(\*', Comment, 'comment'),
            (r'"', String.Double, 'string'),

            (r'\d[\d_]*', Number.Integer),
            (r'0[xX][\da-fA-F][\da-fA-F_]*', Number.Hex),
            (r'0[oO][0-7][0-7_]*', Number.Oct),
            (r'0[bB][01][01_]*', Number.Bin),
            (r'-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)', Number.Float),
        ],
        'docstring': comment(String.Doc),
        'comment': comment(Comment),
        'string': [
            (r'[^"]+', String.Double),
            (r'""', String.Double),
            (r'"', String.Double, '#pop'),
        ],

        '_vernac': [
            (r"{}(\s+)({})".format(decls_re, name_re),
             bygroups(Keyword.Namespace, Text, Name.Function),
             'binders'),
            (expects_binders_re,
             Keyword.Namespace,
             'binders'),
            (r"{}(\s+)({})".format(expects_name_re, name_re),
             bygroups(Keyword.Namespace, Text, Name.Function)),
            (opts_re, Keyword.Namespace),
            (tables_re, Keyword.Namespace),
            (ws(cmd), Keyword.Namespace),
        ],
        'binders': binders(r":=|[.]", name_re),

        '_keywords': [
            (r"\bforall|exists|∀|∃\b", Keyword.Reserved, 'quantifier args'),
            (r"\bfun\b", Keyword.Reserved, 'fun args'),
            (ws(kwds['ltac-keywords']), Keyword.Reserved),
            (ws(kwds['ltac-builtins']), Keyword.Pseudo),
            (ws(kwds['gallina-keywords']), Keyword.Reserved),
            (ws(kwds['gallina-constants']), Keyword.Type),
            (ws(kwds['tacn']), Name.Builtin),
            # FIXME terminator tactics Name.Builtin.Pseudo
        ],
        'quantifier args': binders(",", name_re),
        'fun args': binders("=>", name_re),
        'in parens': [
            (r"\(", Operator, '#push'),
            (r"\)", Operator, '#pop'),
            include('_gallina'),
        ],
        'type annot': [
            (':', Operator, '#pop'),
            (name_re, Name.Variable),
            include('_basic'),
            default("#pop"),
        ],

        '_other': [
            (name_re, Name),
            (r"[{}]+".format(symbol), Operator),
        ],
    }

    def analyse_text(text):
        if text.startswith('(*'):
            return True
