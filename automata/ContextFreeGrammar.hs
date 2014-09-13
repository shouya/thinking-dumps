-- A Context-Free Grammar Library
module ContextFreeGrammar


data BNF a = [Rule a]
data Rule a = Rule { ruleName :: String
                   , ruleDef  :: [RuleDef a]
                   }
data RuleDef a = (Terminal a) => Term a
               | RuleRef String
               | ConcatOf [RuleDef a]
