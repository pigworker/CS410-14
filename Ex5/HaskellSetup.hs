module HaskellSetup where

{- This is the low-level stuff that hooks into the ncurses library, together
with the Haskell versions of the Agda types. You should not need to bother
reading or modifying this file. -}

import Debug.Trace
import Foreign
import Foreign.C (CInt(..))
import ANSIEscapes
import System.IO
import System.Environment
import Control.Applicative
import Control.Concurrent

foreign import ccall
  initscr :: IO () 

foreign import ccall "endwin"
  endwin :: IO CInt

foreign import ccall "refresh"
  refresh :: IO CInt

foreign import ccall "&LINES"
  linesPtr :: Ptr CInt

foreign import ccall "&COLS"
  colsPtr :: Ptr CInt

scrSize :: IO (Int, Int)
scrSize = do
    lnes <- peek linesPtr
    cols <- peek colsPtr
    return (fromIntegral cols, fromIntegral lnes)

data Direction = DU | DD | DL | DR deriving Show
data Modifier = Normal | Shift | Control deriving Show
data Key = Char Char | Arrow Modifier Direction | Enter | Backspace | Delete | Escape deriving Show

data Nat = Zero | Suc Nat
toNat :: Int -> Nat
toNat 0 = Zero
toNat n = Suc (toNat (n - 1))
fromNat :: Nat -> Int
fromNat Zero = 0
fromNat (Suc n) = 1 + fromNat n

data EQ a b c = Refl

data Change = AllQuiet | CursorMove | LineEdit | BigChange

data Action = GoRowCol Nat Nat | SendText [Char]

act :: Action -> IO ()
act (GoRowCol y x) = do
  resetCursor
  forward (fromNat x)
  down (fromNat y)
act (SendText s) = putStr s

getEscapeKey :: [(String, Key)] -> IO (Maybe Key)
getEscapeKey [] = return Nothing
getEscapeKey sks = case lookup "" sks of
  Just k -> return (Just k)
  _ -> do
    c <- getChar
    getEscapeKey [(cs, k) | (d : cs, k) <- sks, d == c]

directions :: [(Char, Direction)]
directions = [('A', DU), ('B', DD),
              ('C', DR), ('D', DL)]

escapeKeys :: [(String, Key)]
escapeKeys =
  [([c], Arrow Normal d) | (c, d) <- directions] ++
  [("1;2" ++ [c], Arrow Shift d) | (c, d) <- directions] ++
  [("1;5" ++ [c], Arrow Control d) | (c, d) <- directions] ++
  [("3~", Delete)]

keyReady :: IO (Maybe Key)
keyReady = do
  b <- hReady stdin
  if not b then return Nothing else do
    c <- getChar
    case c of
      '\n' -> return $ Just Enter
      '\r' -> return $ Just Enter
      '\b' -> return $ Just Backspace
      '\DEL' -> return $ Just Backspace
      _ | c >= ' ' -> return $ Just (Char c)
      '\ESC' -> do
        b <- hReady stdin
        if not b then return $ Just Escape else do
          c <- getChar
          case c of
            '[' -> getEscapeKey escapeKeys
            _ -> return $ Just Escape
      _ -> return $ Nothing

pni :: (Int, Int) -> (Nat, Nat)
pni (y, x) = (toNat y, toNat x)

mainLoop ::
  ([[Char]] -> b) ->
  (Key -> b -> (Change, b)) ->
  ((Nat, Nat) -> (Nat, Nat) -> (Change, b) -> ([Action], (Nat, Nat))) ->
  IO ()
mainLoop initBuf keystroke render = do
  hSetBuffering stdout NoBuffering
  hSetBuffering stdin NoBuffering
  xs <- getArgs
  buf <- case xs of
    [] -> return (initBuf [])
    (x : _) -> (initBuf . lines) <$> readFile x
  initscr
  innerLoop (0, 0) (Zero, Zero) (BigChange, buf)
  endwin
  return ()
  where
    innerLoop oldSize topLeft (c, b) = do
      refresh
      size <- scrSize
      (acts, topLeft) <- return $
        if size /= oldSize
          then render (pni size) topLeft (BigChange, b)
          else render (pni size) topLeft (c, b)
      mapM_ act acts
      mc <- keyReady
      case mc of
        Nothing -> threadDelay 100 >> innerLoop size topLeft (AllQuiet, b)
        Just k -> innerLoop size topLeft (keystroke k b)
