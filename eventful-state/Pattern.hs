{-# LANGUAGE DeriveFunctor #-}

module Pattern where

import qualified Data.Map.Strict as Map
import           Data.Word (Word8)
import Data.Maybe (catMaybes, fromJust, isJust)
import Control.Applicative ((<$>), pure)

data Value = VS { svalue :: String   }
           | VF { fvalue :: Double   }
           | VR { rvalue :: Rational }
           | VI { ivalue :: Int      }
           | VB { bvalue :: Bool     }
           | VX { xvalue :: [Word8]  } -- Used for OSC 'blobs'
           | VState {statevalue ::  State -> Value -> State}

-- | Time is rational
type Time = Rational

-- A timespan has a beginning and end
data Arc = Arc
  { start :: Time
  , stop  :: Time
  } deriving (Eq, Ord, Show)

-- | State is a dictionary of patterns
type State = Map.Map String (Pattern Value)

-- | A value with a timespan. The value is a fraction of a whole,
-- apart from 'continuous' events, which don't have wholes.
data Event a = Event
  { whole :: Maybe Arc
  , part :: Arc
  , value :: a
  } deriving (Eq, Ord, Functor)

-- | A pattern is a function from a timespan, to the events active in
-- that timespan.
data Pattern a = Pattern {query :: Arc -> [Event a]}

-- Instances

instance Functor Pattern where
  -- | apply a function to all the values in a pattern
  fmap f p = p {query = fmap (fmap f) . query p}

instance Applicative Pattern where
  -- | Continuous event that lasts forever (as opposed to current
  -- implementation where there is one event for cycle
  pure v = Pattern $ \a -> [Event Nothing a v]
  (<*>) = applyPatToPatBoth

-- Event Filters

-- | Remove events from patterns that do not meet the given test
filterValues :: (a -> Bool) -> Pattern a -> Pattern a
filterValues f p = p {query = filter (f . value) . query p}

-- | Turns a pattern of 'Maybe' values into a pattern of values
filterJust :: Pattern (Maybe a) -> Pattern a
filterJust p = fromJust <$> filterValues isJust p

filterWhen :: (Time -> Bool) -> Pattern a -> Pattern a
filterWhen test p = p {query = filter (test . wholeStart) . query p}

filterOnsets :: Pattern a -> Pattern a
filterOnsets p = p {query = filter (\e -> eventPartStart e == wholeStart e) . query (filterDigital p)}

filterEvents :: (Event a -> Bool) -> Pattern a -> Pattern a
filterEvents f p = p {query = filter f . query p}

filterDigital :: Pattern a -> Pattern a
filterDigital = filterEvents isDigital

filterAnalog :: Pattern a -> Pattern a
filterAnalog = filterEvents isAnalog

-- Applicative

applyPatToPatBoth :: Pattern (a -> b) -> Pattern a -> Pattern b
applyPatToPatBoth pf px = Pattern q
    where q st = catMaybes $ (concatMap match $ query pf st) ++ (concatMap matchX $ query (filterAnalog px) st)
            where
              -- match analog events from pf with all events from px
              match ef@(Event Nothing fPart _)   = map (withFX ef) (query px fPart) -- analog
              -- match digital events from pf with digital events from px
              match ef@(Event (Just fWhole) _ _) = map (withFX ef) (query (filterDigital px) $ fWhole) -- digital
              -- match analog events from px (constrained above) with digital events from px
              matchX ex@(Event Nothing fPart _)  = map (\ef -> withFX ef ex) (query (filterDigital pf) fPart) -- digital
              matchX _ = error "can't happen"
              withFX ef ex = do whole' <- subMaybeArc (whole ef) (whole ex)
                                part' <- subArc (part ef) (part ex)
                                return (Event whole' part' (value ef $ value ex))

-- Instances


-- Time utilities

-- | The 'sam' (start of cycle) for the given time value
sam :: Time -> Time
sam = fromIntegral . (floor :: Time -> Int)

-- | Turns a number into a (rational) time value. An alias for 'toRational'.
toTime :: Real a => a -> Rational
toTime = toRational

-- | The end point of the current cycle (and starting point of the next cycle)
nextSam :: Time -> Time
nextSam = (1+) . sam

-- | The position of a time value relative to the start of its cycle.
cyclePos :: Time -> Time
cyclePos t = t - sam t

-- | @subArc i j@ is the timespan that is the intersection of @i@ and @j@.
-- intersection
-- The definition is a bit fiddly as results might be zero-width, but
-- not at the end of an non-zero-width arc - e.g. (0,1) and (1,2) do
-- not intersect, but (1,1) (1,1) does.
subArc :: Arc -> Arc -> Maybe Arc
subArc a@(Arc s e) b@(Arc s' e')
  | and [s'' == e'', s'' == e, s < e] = Nothing
  | and [s'' == e'', s'' == e', s' < e'] = Nothing
  | s'' <= e'' = Just (Arc s'' e'')
  | otherwise = Nothing
  where (Arc s'' e'') = sect a b

sect :: Arc -> Arc -> Arc
sect (Arc s e) (Arc s' e') = Arc (max s s') (min e e')

-- | convex hull union
hull :: Arc -> Arc -> Arc
hull (Arc s e) (Arc s' e') = Arc (min s s') (max e e')

subMaybeArc :: Maybe Arc -> Maybe Arc -> Maybe (Maybe Arc)
subMaybeArc (Just a) (Just b) = do sa <- subArc a b
                                   return $ Just sa
subMaybeArc _ _ = Just Nothing

-- | The arc of the whole cycle that the given time value falls within
timeToCycleArc :: Time -> Arc
timeToCycleArc t = Arc (sam t) (sam t + 1)

-- | Shifts an arc to the equivalent one that starts during cycle zero
cycleArc :: Arc -> Arc
cycleArc (Arc s e) = Arc (cyclePos s) (cyclePos s + (e-s))

-- | A list of cycle numbers which are included in the given arc
cyclesInArc :: Integral a => Arc -> [a]
cyclesInArc (Arc s e)
  | s > e = []
  | s == e = [floor s]
  | otherwise = [floor s .. ceiling e-1]

-- | A list of arcs of the whole cycles which are included in the given arc
cycleArcsInArc :: Arc -> [Arc]
cycleArcsInArc = map (timeToCycleArc . (toTime :: Int -> Time)) . cyclesInArc

-- | Splits the given 'Arc' into a list of 'Arc's, at cycle boundaries.
arcCycles :: Arc -> [Arc]
arcCycles (Arc s e) | s >= e = []
                | sam s == sam e = [Arc s e]
                | otherwise = Arc s (nextSam s) : arcCycles (Arc (nextSam s) e)

-- | Like arcCycles, but returns zero-width arcs
arcCyclesZW :: Arc -> [Arc]
arcCyclesZW (Arc s e) | s == e = [Arc s e]
                  | otherwise = arcCycles (Arc s e)

-- | Similar to 'fmap' but time is relative to the cycle (i.e. the
-- sam of the start of the arc)
mapCycle :: (Time -> Time) -> Arc -> Arc
mapCycle f (Arc s e) = Arc (sam' + f (s - sam')) (sam' + f (e - sam'))
         where sam' = sam s

-- | @isIn a t@ is @True@ if @t@ is inside
-- the arc represented by @a@.
isIn :: Arc -> Time -> Bool
isIn (Arc s e) t = t >= s && t < e


wholeOrPart :: Event a -> Arc
wholeOrPart (Event {whole = Just a}) = a
wholeOrPart e = part e

-- | Get the onset of an event's 'whole'
wholeStart :: Event a -> Time
wholeStart = start . wholeOrPart

-- | Get the offset of an event's 'whole'
wholeStop :: Event a -> Time
wholeStop = stop . wholeOrPart

-- | Get the onset of an event's 'whole'
eventPartStart :: Event a -> Time
eventPartStart = start . part

-- | Get the offset of an event's 'part'
eventPartStop :: Event a -> Time
eventPartStop = stop . part

-- | Get the timespan of an event's 'part'
eventPart :: Event a -> Arc
eventPart = part

eventValue :: Event a -> a
eventValue = value

eventHasOnset :: Event a -> Bool
eventHasOnset e | isAnalog e = False
                | otherwise = start (fromJust $ whole e) == start (part e)

isAnalog :: Event a -> Bool
isAnalog (Event {whole = Nothing}) = True
isAnalog _ = False

isDigital :: Event a -> Bool
isDigital = not . isAnalog

