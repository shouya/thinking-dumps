{-# LANGUAGE FlexibleContexts #-}

{-
this program is a practice to play around with monad transformers.
-}

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Trans
import Control.Monad.Identity

import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust)


type Var   = String
data Value = IntVal Integer
           | Closure Env Var Expr

instance Show Value where
  show (IntVal i)      = "int: " ++ show i
  show (Closure _ _ _) = "some closure"

data Expr = App Expr Expr
          | Abs Var Expr
          | Id Var
          | Lit Integer
          | Plus Expr Expr


type Env = Map Var Value


emptyEnv = M.empty


eval0 :: Expr -> Env -> Value
eval0 (App e1 e2) env = let ee1 = eval0 e1 env
                            ee2 = eval0 e2 env
                        in case ee1 of
                            Closure env' v e ->
                              let newenv = M.insert v ee2 env'
                              in eval0 e newenv
eval0 (Abs v e) env  = Closure env v e
eval0 (Id v) env     = fromJust $ M.lookup v env
eval0 (Lit i) env    = IntVal i
eval0 (Plus a b) env = let IntVal ea = eval0 a env
                           IntVal eb = eval0 b env
                       in IntVal $ ea + eb


-- should result in 7
testexpr0 = (App (Abs "v" (Plus (Id "v") (Lit 3)))
                (Plus (Lit 3) (Lit 1)))

-- eval0 testexpr0 emptyEnv



-- error handling version using ExceptT: eval1
type Eval1 a = ExceptT String Identity a

eval1 :: Expr -> Env -> Eval1 Value
eval1 (App e1 e2) env = do ee1 <- eval1 e1 env
                           ee2 <- eval1 e2 env
                           case ee1 of
                            Closure env' v e ->
                              let newenv = M.insert v ee2 env'
                              in eval1 e newenv
                            _ -> throwError "not a function meow~"
eval1 (Abs v e) env  = return $ Closure env v e
eval1 (Id v) env     = case M.lookup v env of
                        Just v  -> return v
                        Nothing -> throwError ("var " ++ v ++
                                               " not found meow~")
eval1 (Lit i) env    = return $ IntVal i
eval1 (Plus a b) env = do IntVal ea <- eval1 a env
                          IntVal eb <- eval1 b env
                          return $ IntVal $ ea + eb


-- "v" is not found in the scope
testexpr1 = (App (Abs "m" (Plus (Id "v") (Lit 3)))
                 (Plus (Lit 3) (Lit 1)))

-- eval1 testexpr1 emptyEnv




-- env param eliminating version using ReaderT: eval2
-- type Eval2 a = ReaderT Env Eval1 a
type Eval2 a = ReaderT Env (ExceptT String Identity) a

eval2 :: Expr -> Eval2 Value
eval2 (App e1 e2) = do ee1 <- eval2 e1
                       ee2 <- eval2 e2
                       case ee1 of
                        Closure env' v e -> do
                          local (const $ M.insert v ee2 env') $ eval2 e
                        _ -> throwError "not a function meow~"
eval2 (Abs v e)  = do env <- ask
                      return $ Closure env v e
eval2 (Id v)     = do env <- ask
                      case M.lookup v env of
                        Just v  -> return v
                        Nothing -> throwError ("var " ++ v ++
                                               " not found meow~")
eval2 (Lit i)    = return $ IntVal i
eval2 (Plus a b) = do IntVal ea <- eval2 a
                      IntVal eb <- eval2 b
                      return $ IntVal $ ea + eb


testexpr2 = (App (Abs "v" (Plus (Id "v") (Lit 3)))
                 (Plus (Lit 3) (Lit 1)))
-- runReaderT (eval2 testexpr2) emptyEnv     => 7



-- instructions counting version using StateT: eval3
type Eval3 a = StateT Integer (ReaderT Env (ExceptT String Identity)) a

-- tick :: Eval3 ()
-- tick = modify (+1)

tick :: (MonadState Integer m) => m ()
tick = modify (+1)

eval3 :: Expr -> Eval3 Value
eval3 (App e1 e2) = do ee1 <- eval3 e1
                       ee2 <- eval3 e2
                       case ee1 of
                        Closure env' v e -> do
                          tick
                          local (const $ M.insert v ee2 env') $ eval3 e
                        _ -> throwError "not a function meow~"
eval3 (Abs v e)  = do env <- ask
                      tick
                      return $ Closure env v e
eval3 (Id v)     = do env <- ask
                      case M.lookup v env of
                        Just v  -> tick >> return v
                        Nothing -> throwError ("var " ++ v ++
                                               " not found meow~")
eval3 (Lit i)    = do tick
                      return $ IntVal i
eval3 (Plus a b) = do IntVal ea <- eval3 a
                      IntVal eb <- eval3 b
                      tick
                      return $ IntVal $ ea + eb


-- should tick 8 times, i.e. returns (IntVal 7, 8)
testexpr3 = (App (Abs "v" (Plus (Id "v") (Lit 3)))
                 (Plus (Lit 3) (Lit 1)))
-- runReaderT (runStateT (eval3 testexpr3) 0) emptyEnv



-- logging version using WriterT: eval4
type Eval4 a = WriterT [String] (StateT Integer (ReaderT Env (ExceptT String Identity))) a

eval4 :: Expr -> Eval4 Value
eval4 (App e1 e2) = do ee1 <- eval4 e1
                       ee2 <- eval4 e2
                       tell ["i'm applying, excited!"]
                       case ee1 of
                        Closure env' v e -> do
                          tick
                          local (const $ M.insert v ee2 env') $ eval4 e
                        _ -> throwError "not a function meow~"
eval4 (Abs v e)  = do env <- ask
                      tick
                      return $ Closure env v e
eval4 (Id v)     = do env <- ask
                      tell ["i'm being looking up!"]
                      case M.lookup v env of
                        Just v  -> tick >> return v
                        Nothing -> throwError ("var " ++ v ++
                                               " not found meow~")
eval4 (Lit i)    = do tick
                      return $ IntVal i
eval4 (Plus a b) = do IntVal ea <- eval4 a
                      IntVal eb <- eval4 b
                      tick
                      return $ IntVal $ ea + eb


-- should tick 8 times, i.e. returns (IntVal 7, 8)
testexpr4 = (App (Abs "v" (Plus (Id "v") (Lit 3)))
                 (Plus (Lit 3) (Lit 1)))
-- runReaderT (runStateT (runWriterT (eval4 testexpr4)) 0) emptyEnv






-- chatterbox version with IO: eval5
type Eval5 a = WriterT [String] (StateT Integer (ReaderT Env (ExceptT String IO))) a

eval5 :: Expr -> Eval5 Value
eval5 (App e1 e2) = do ee1 <- eval5 e1
                       ee2 <- eval5 e2
                       tell ["i'm applying, excited!"]
                       liftIO $ putStrLn ("i'd to say that i was " ++
                                          "applied and logged that line")
                       case ee1 of
                        Closure env' v e -> do
                          tick
                          local (const $ M.insert v ee2 env') $ eval5 e
                        _ -> throwError "not a function meow~"
eval5 (Abs v e)  = do env <- ask
                      tick
                      liftIO $ putStrLn "oh it hurts! stop abstracting on me!!"
                      return $ Closure env v e
eval5 (Id v)     = do env <- ask
                      tell ["i'm being looking up!"]
                      case M.lookup v env of
                        Just v  -> tick >> return v
                        Nothing -> throwError ("var " ++ v ++
                                               " not found meow~")
eval5 (Lit i)    = do tick
                      liftIO $ putStrLn ("what is that literal? is it " ++
                                         (show (i + 1)) ++ "? of course not.")
                      return $ IntVal i
eval5 (Plus a b) = do IntVal ea <- eval5 a
                      IntVal eb <- eval5 b
                      tick
                      return $ IntVal $ ea + eb


-- should output a lot of gibberish when being evaluated
testexpr5 = (App (Abs "v" (Plus (Id "v") (Lit 3)))
                 (Plus (Lit 3) (Lit 1)))
-- runExceptT (runReaderT (runStateT (runWriterT (eval5 testexpr5)) 0) emptyEnv)
