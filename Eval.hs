module Eval where

import qualified Data.Map as M
import Parseur


--------------------------------------------------------------------------------
-- Les expressions et la traduction de Sexp en expression (Exp)
--------------------------------------------------------------------------------

-- type a = b indique que a est un synonyme de b
-- il ne s'agit pas vraiment d'un nouveau type
type Type = Symbol
type Constructor = Symbol
type DataConstructor = (Constructor, [Type])

type CasePattern = (Symbol, [Symbol], Exp)

data Mutability = Constant
                | Mutable
                deriving (Eq, Show)

data Scope = Lexical
           | Dynamic
           deriving (Eq, Show)

-- Les expressions du langages ouf
-- Vous n'avez pas à modifier ce datatype
data Exp = EInt Int
         | EVar Symbol
         | EDefine Symbol Exp
         | EApp Exp Exp
         | ELam Symbol Exp
         | ESet Symbol Exp
         | ELet [(Symbol, Exp)] Exp
         | EData Type [DataConstructor]
         | ECase Exp [CasePattern]
         | EOufScope Symbol Scope
         | EOufMutability Symbol Mutability
         deriving (Eq, Show)

type Error = String

reservedKeywords :: [Symbol]
reservedKeywords = ["lambda", "let", "case", "data", "define", "set", "ouf", "Error"]

caseFonctionKeywords :: [Symbol]
caseFonctionKeywords = ["+","-","*"]

var2Exp :: Sexp -> Either Error Exp
var2Exp (SSym ident) = Right $ EVar ident
var2Exp _ = Left "Doit être un identificateur"

var2Symbol :: Sexp -> Either Error Symbol
var2Symbol (SSym ident) = Right ident
var2Symbol _ = Left "Doit être un identificateur"

-- Vous devez compléter une partie cette fonction
sexp2Exp :: Sexp -> Either Error Exp
sexp2Exp (SNum x) = Right $ EInt x
sexp2Exp (SSym ident) =
  if ident `elem` reservedKeywords
  then Left $ ident ++ " is a reserved keyword"
  else Right $ EVar ident

sexp2Exp (SList ls@((SSym s) : xs))
  | s `elem` reservedKeywords = specialForm2Exp ls

sexp2Exp (SList (func : [])) =  Left "Function application must provide at least one parameter"

-- Il faut écrire le cas pour les fonctions (Ex : Right (EApp (EVar "+") (EApp (EVar "x") (EVar "y"))))
sexp2Exp (SList (func : args)) = do
                                  function <- sexp2Exp func
                                  arguments <- sequence $ map sexp2Exp args
                                  return $ foldr (\expr1 expr2 -> EApp expr2 expr1)
                                                 (EApp function (head arguments))
                                                 (tail arguments)

sexp2Exp _ = Left "Erreur de syntaxe"

-- Il faut compléter cette fonction qui gère
-- toutes les formes spéciales (lambda, let ...)
specialForm2Exp :: [Sexp] -> Either Error Exp
specialForm2Exp ((SSym "lambda") : (SList []) : _ : []) = Left "Syntax Error : No parameter"

specialForm2Exp ((SSym "lambda") : (SList params) : body : []) = do
                                                                    body' <- sexp2Exp body
                                                                    params' <- sequence $ map var2Symbol ((tail params) ++ [head params])
                                                                    return $ foldl (\b s -> ELam s b)
                                                                                   (ELam (head params') body')
                                                                                   (tail params')

specialForm2Exp ((SSym "define") : (SSym []) : _ : []) = Left "Variable cannot be empty"

specialForm2Exp ((SSym "define") : (SSym variableName) : body : []) =  do
                                                                    body' <- sexp2Exp body
                                                                    return $ EDefine variableName body'

specialForm2Exp ((SSym "define") : (SSym variableName) : lamIdentifier@(SSym "lambda") : param : body : []) =  do
                                                                    body' <- specialForm2Exp (lamIdentifier:param:body:[])
                                                                    return $ EDefine variableName body'


specialForm2Exp ((SSym "let") : _ : []) = Left "No variables declaration (if empty put '()')"

-- fonction de retour est un numero, donc on retourne le numero
specialForm2Exp ((SSym "let") : _ : numero@(SNum r) : []) = sexp2Exp numero

--Si la fonction est une variable Ex : (let ((a 1)) a)
specialForm2Exp ((SSym "let") : variables : singleFunction@(SSym f) : []) = do
                                                                                tuple <- listToTupleList variables
                                                                                function <- var2Exp singleFunction
                                                                                return (ELet tuple function)

--Si la fonction dans le in est une autre foncttion Ex : (let ((x 3) (y 7)) (+ x y))
specialForm2Exp ((SSym "let") : variables@(SList v) : composeFunction@(SList f) : []) = do
                                                                                    tuple <- listToTupleList variables
                                                                                    function <- sexp2Exp composeFunction
                                                                                    return (ELet tuple function)

-- data1 et data2 est une SList
-- EData Type(Symbol) [DataConstructor] ; DataConstructor = (Symbol, [Symbol])
specialForm2Exp ((SSym "data") : (SSym dataName) : data1@(SList d1) : data2@(SList d2) : []) = do
                                                                                            data1' <- dataConstructor data1
                                                                                            data2' <- dataConstructor data2
                                                                                            return (EData dataName (data1':data2':[]))
--ECase Exp [CasePattern]
--CasePattern = (Symbol, [Symbol], Exp)
specialForm2Exp ((SSym "case") : valueToTest@(SSym c) : body@(SList b) : []) = if c `elem` caseFonctionKeywords
                                                                          then Left "Name of case can be a function"
                                                                          else do
                                                                            valueToTest' <- sexp2Exp valueToTest
                                                                            casePattern <- casePatternConstructor body
                                                                            return (ECase valueToTest' casePattern)

specialForm2Exp ((SSym "ouf") : (SSym "scope") : (SSym variable) : (SSym scope) : []) = case scope of
                                                                                          "lexical" -> Right (EOufScope variable Lexical)
                                                                                          "dynamic" -> Right (EOufScope variable Dynamic)
                                                                                          _ -> Left "Scope does not exist"

specialForm2Exp ((SSym "ouf") : (SSym "mutability") : (SSym variable) : (SSym scope) : []) = case scope of
                                                                                          "variable" -> Right (EOufMutability variable Mutable)
                                                                                          "constant" -> Right (EOufMutability variable Constant)
                                                                                          _ -> Left "Scope does not exist"


specialForm2Exp ((SSym "set") : (SSym variableName) : value : []) = do
                                                                        value' <- sexp2Exp value
                                                                        return $ ESet variableName value'

specialForm2Exp _ = Left "Syntax Error : Unknown special form"

-- fonction qui construit l'environnement pour le 'let'
listToTupleList :: Sexp -> Either Error [(Symbol, Exp)]
listToTupleList (SList []) = Right []
listToTupleList (SList( SList((SSym symbol) : expr : []) : list)) = do
                              expression <- sexp2Exp expr
                              nextResult <- listToTupleList $ SList list
                              return $ (symbol, expression) : nextResult
listToTupleList _ = Left "Error, list not well constructed"

-- fonction qui construit le data constructor pour 'data'
dataConstructor :: Sexp -> Either Error (Constructor, [Type])
dataConstructor (SList(SSym singleDef : [])) = Right (singleDef, [])
dataConstructor (SList(SSym multipleDef : types)) = Right (multipleDef, (sexpListToListOfTypes types))

sexpListToListOfTypes :: [Sexp] -> [Type]
sexpListToListOfTypes [] = []
sexpListToListOfTypes (SSym(type'):types) =  ((type'):(sexpListToListOfTypes types))

--ECase Exp [CasePattern]
--CasePattern = (Symbol, [Symbol], Exp)
casePatternConstructor :: Sexp -> Either Error [CasePattern]
casePatternConstructor (SList []) = Right []
casePatternConstructor (SList(SList(definition@(SList d) : returnValue : []): others)) = do
                                                                          returnValue' <- sexp2Exp returnValue
                                                                          nextResult <- casePatternConstructor $ SList others
                                                                          dataCase <- dataConstructor definition
                                                                          return ((tupleToTriple dataCase returnValue') : nextResult)
tupleToTriple :: (a,b) -> c -> (a,b,c)
tupleToTriple (a,b) c = (a,b,c)

mangle :: [Symbol] -> [Symbol]
mangle [] = []
mangle (x:xs) = xs ++ [x]
--------------------------------------------------------------------------------
-- L'évaluation
--------------------------------------------------------------------------------

-- @ + variableName : signifie que la variable a une valeur de mutability
-- ! + variableName : signifie que la variable a une valeur de portée

-- Les valeurs retournées par l'évaluateur
-- Vous n'avez pas à modifier ce datatype
data Value = VInt Int
           | VLam Symbol Exp LexicalEnv
           | VPrim (Value -> Value)
           | VData Type Type [Value]
           | VUnit
           | VScope Scope
           | VMutability Mutability
           | VDebugger Exp

instance Show Value where
  show (VInt n) = show n
  show (VData t c d) = "VData " ++ t ++ " (" ++
    (unwords $ show c : map show d) ++ ")"
  show VUnit = "VUnit"
  show (VPrim _) = "<primitive>"
  show (VLam s e env) = "VLamda [" ++ s ++ (unwords [",", show e, ",", show env])
    ++ "]"
  show (VDebugger n) = show n
  show (VScope n) = show n
  show (VMutability n) = show n

instance Eq Value where
  (VInt n1) == (VInt n2) = n1 == n2
  VUnit == VUnit = True
  (VData t1 c1 d1) == (VData t2 c2 d2) =
     t1 == t2 && c1 == c2 && d1 == d2
  -- Functions and primitives are not comparable
  _ == _ = False

-- Un environnement pour portée lexicale
-- Vous n'avez pas à modifier ce datatype
type LexicalEnv = [(Symbol, Value)]

-- L'environnement. Au début, comme celui de la portée lexicale
-- Vous devrez modifier ce type pour la portée dynamique
-- et les instructions ouf
type Env = LexicalEnv

-- lookup de la librairie standard utilise Maybe
-- au lieu de Either
lookup2 :: [(Symbol, a)] -> Symbol -> Either Error a
lookup2 [] sym = Left $ "Not in scope " ++ sym
lookup2 ((s, v) : _) sym | s == sym = Right v
lookup2 (_ : xs) sym = lookup2 xs sym

-- Recherche un identificateur dans l'environnement
lookupVar :: Env -> Symbol -> Either Error Value
lookupVar = lookup2

-- Ajoute une variable dans l'environnement
insertVar :: Env -> Symbol -> Value -> Env
insertVar e s v =  (s, v) : e

-- Insert plusieurs variables dans l'environnement
-- La première variable de la liste est la dernière insérée
insertVars :: Env -> [(Symbol, Value)] -> Env
insertVars env xs = foldr (\(s, v) env -> insertVar env s v) env xs

primDef :: [(Symbol, Value)]
primDef = [("+", prim (+)),
           ("-", prim (-)),
           ("*", prim (*))]
  where prim op = VPrim (\ (VInt x) -> VPrim (\ (VInt y) -> VInt (x `op` y)))

envEmpty :: Env
envEmpty = []

env0 :: Env
env0 = insertVars envEmpty primDef


-- L'évaluateur au niveau global
-- L'évaluateur retourne une valeur et un environnement mis à jour
-- L'environnement mis à jour est utile pour de nouvelles définitions
-- avec define ou data ou lorsque les variables sont
-- modifiées par set par exemple.
evalGlobal :: Env -> Exp -> Either Error (Env, Value)
evalGlobal env (EDefine variableName expression) = do
                                                      valueOfExpression <- eval env expression
                                                      Right ((insertVar env (variableName) $ snd valueOfExpression),snd valueOfExpression)

-- EData Type(Symbol) [DataConstructor] = (Constructor, [Type])
-- to VData Type Type [Value]
evalGlobal env (EData dataName definition) = let
                                                def1 = (fst $ head definition)
                                                def2 = (fst $ last definition)
                                                def2Parameters = (typesToValues (snd $ last definition))
                                                globalData = (VData def1 def2 (def2Parameters))
                                                envGlobalData = insertVar env dataName globalData
                                                envAfterDef1 = insertVar envGlobalData def1 (VData def1 "0" [])
                                                envAfterDef2 = insertVar envAfterDef1 def2 (VData def2 ("" ++ (show $ length def2Parameters))  [])
                                                in Right (envAfterDef2, globalData)

evalGlobal env (ESet variableName expression) = case (lookupVar env ("@" ++ variableName)) of
                                                            Right (VMutability Mutable) -> evalGlobal env (EDefine variableName expression )
                                                            _ -> Left "Variable is unchangeable"

evalGlobal env e = eval env e -- Autre que Define et Data, eval prend le relais


typesToValues :: [Type] -> [Value]
typesToValues [] = []
typesToValues (type':types) = (typeToValue type'):(typesToValues types)

--VUnit refers to same value of the data being define
typeToValue :: Type -> Value
typeToValue "Int" = VInt 0
typeToValue _ = VUnit

-- L'évaluateur pour les expressions
eval :: Env -> Exp -> Either Error (Env, Value)
eval _ (EDefine _ _) = Left $ "Define must be a top level form"
eval _ (EData _ _) = Left $ "Data must be a top level form"
eval env (EInt x) = Right (env, VInt x)
eval env (EVar sym) = do
  v <- lookupVar env sym
  return (env, v)

--VLam Symbol Exp LexicalEnv : [(Symbol, Value)]
eval env (ELam sym body) = Right (env,VLam sym body env)

eval env (EApp function restOfarguments) = do
                                            func <- eval env function
                                            case snd func of
                                              (VPrim f) -> do
                                                            arg <- eval env restOfarguments
                                                            return (env, (f $ snd arg))

                                              (VLam symbol expression tempEnv) -> do
                                                                                arg <- eval env restOfarguments
                                                                                scopeOfExpression <- case (exp2Symbol expression) of
                                                                                                      "Stopper" -> Right (VScope Lexical)
                                                                                                      _ -> case (lookupVar env ("!" ++ (exp2Symbol expression))) of
                                                                                                              Left erro -> Right (VScope Lexical)
                                                                                                              _ -> (lookupVar env ("!" ++ (exp2Symbol expression)))
                                                                                updatedEnv <- case scopeOfExpression of
                                                                                                    (VScope Dynamic) -> case (lookupVar tempEnv ("#" ++ (exp2Symbol expression))) of
                                                                                                                                Right _ -> Left "Dynamic values can be accesed"
                                                                                                                                _ -> eval (env ++ ((symbol, snd arg):tempEnv)) expression
                                                                                                    _ ->  eval ((symbol, snd arg):tempEnv) expression
                                                                                return (env, snd updatedEnv)

                                              (VData typeGlobal nbParameters params) -> case nbParameters of
                                                                                            "0" -> Left "Too many parameters"
                                                                                            _ -> do
                                                                                                       args <- eval env restOfarguments
                                                                                                       return (env, (VData typeGlobal (nbParametersUpdate nbParameters) (params ++ ((snd args):[]))))


                                              _ -> Left "Too many parameters"

-- valeur de retourn du Let : ELet [(Symbol, Exp)] Exp
eval env (ELet variables expression) = do
                                          letEnv <- makeLetEnv env variables
                                          result <- eval (letEnv ++ env) expression
                                          return (env,snd result)

--ECase Exp [CasePattern]
-- CasePattern : (Symbol, [Symbol], Exp)
eval env (ECase e patterns) = do
                                  expressionToEval <- eval env e
                                  case snd expressionToEval of
                                    (VData typeGlobal nbParameters params) -> do
                                                                                result <- (casePatternMatch env typeGlobal patterns params)
                                                                                return (env, result)
                                    _ -> Left "Error : case only takes data as the first parameter"



eval env (EOufScope sym scope) = case scope of
                                    Lexical ->  Right ((insertVar env ("!" ++ sym) (VScope scope)), VScope scope)
                                    Dynamic ->  Right ((insertVar env ("!" ++ sym) (VScope scope)), VScope scope)

eval env (EOufMutability sym mutability) = case mutability of
                                                    Mutable ->  Right ((insertVar env ("@" ++ sym) (VMutability mutability)), VMutability mutability)
                                                    Constant ->  Right ((insertVar env ("@" ++ sym) (VMutability mutability)), VMutability mutability)

eval env _ = Left "Expression is not recongnized"

makeLetEnv :: Env -> [(Symbol, Exp)] -> Either Error Env
makeLetEnv localEnv [] = Right []
makeLetEnv localEnv ((symbol,expression) : reste) = do
                                                      value <- eval localEnv expression
                                                      loop <- makeLetEnv (("#"++symbol,VUnit):(symbol, snd value):localEnv) reste
                                                      return (("#"++symbol,VUnit):(symbol, snd value) : loop)

nbParametersUpdate :: Type -> Type
nbParametersUpdate nbParameters = show( (read nbParameters :: Int) - 1)

argumentsToListOfValues :: Env -> Exp -> Either Error [Value]
argumentsToListOfValues env expr = (do
                                              value <- eval env expr
                                              return ((snd value) : []))

casePatternMatch :: Env -> Symbol -> [CasePattern] -> [Value] -> Either Error Value
casePatternMatch env patternMatch [] values = Left "Pattern not found"
casePatternMatch env patternMatch (pattern:patterns) values = if (casePatternFirstValue pattern) == patternMatch then
                                                                do
                                                                  caseEnv <- (constructTempCaseEnv (casePatternSecondValue pattern) values)
                                                                  result <- eval (env ++ caseEnv) (casePatternThirdValue pattern)
                                                                  return (snd result)
                                                          else (casePatternMatch env patternMatch patterns values)

constructTempCaseEnv :: [Symbol] -> [Value] -> Either Error Env
constructTempCaseEnv [] [] = Right []
constructTempCaseEnv (symbol:symbols) (value:values) = if (symbols == [] && values /= []) || (symbols /= [] && values == []) then
                                                          Left "Wrong number of parameters"
                                                       else do
                                                              loop <- (constructTempCaseEnv symbols values)
                                                              return ((symbol,value) : loop)

casePatternFirstValue :: CasePattern -> Symbol
casePatternFirstValue (returnValue,_,_) = returnValue

casePatternSecondValue :: CasePattern -> [Symbol]
casePatternSecondValue (_,returnValue,_) = returnValue

casePatternThirdValue :: CasePattern -> Exp
casePatternThirdValue (_,_,returnValue) = returnValue

exp2Symbol :: Exp -> Symbol
exp2Symbol (EVar ident) = ident
exp2Symbol _ = "Stopper"
