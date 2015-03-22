module Check
  ( Property
  , TestOutput
  , property
  , property2
  , property3
  , property4
  , property5
  , property6
  , propertyN
  , property2N
  , property3N
  , property4N
  , property5N
  , check
  , simpleCheck
  , continuousCheck
  , continuousCheckEvery
  , print
  , printVerbose
  , display
  , displayVerbose ) where
{-| Library for doing property-based testing in Elm

# Constructing properties
@docs property, propertyN

# Checking the properties
@docs check, simpleCheck

# Continuously checking properties
@docs continuousCheck, deepContinuousCheck, continuousCheckEvery, deepContinuousCheckEvery

# Printing and displaying results
@docs print, printVerbose, display, displayVerbose

# Properties for functions of multiple parameters
@docs property2, property3, property4, property5, property6, property2N, property3N, property4N, property5N

-}

import Random (Generator, list, generate, initialSeed, Seed, customGenerator, int)
import List (map, map2, filter, length, head, (::), reverse, foldl)
import Dict
import Debug
import Result (Result(..))
import Maybe (Maybe(..), withDefault)
import Time (every, second, Time)
import Signal
import String (join)
import Graphics.Element (Element)
import Text (leftAligned, monospace, fromString)

type alias TestResult =
  { name : String
  , failed : Bool
  , value : String
  , seed : Seed
  }

type alias PartiallyAppliedPredicate a = { unappliedRest : a, revArguments : List String, seed : Seed }

type alias PropertyBuilder a = { name : String, wrappedGenerator : Generator (PartiallyAppliedPredicate a), requestedSamples : Maybe Int }

type alias Property = PropertyBuilder Bool

type alias TestOutput = Dict.Dict String (List TestResult)


{-| Create a property given a number of test cases, a name, a condition to test and a generator
Example :

    doubleNegativeIsPositive =
      propertyN 1000
                "Double Negative is Positive"
                (\number -> -(-number) == number)
                (float -300 400)
-}
propertyN : Int -> String -> (a -> Bool) -> Generator a -> Property 
propertyN numberOfTests name predicate generator = 
  name `describedBy` predicate `on` generator `sample` numberOfTests

{-| Analog of `propertyN` for functions of two arguments
-}
property2N : Int -> String -> (a -> b -> Bool) -> Generator a -> Generator b -> Property
property2N numberOfTests name predicate generatorA generatorB =
  name `describedBy` predicate `on` generatorA `on` generatorB `sample` numberOfTests

{-| Analog of `propertyN` for functions of three arguments
-}
property3N : Int -> String -> (a -> b -> c -> Bool) -> Generator a -> Generator b -> Generator c -> Property
property3N numberOfTests name predicate generatorA generatorB generatorC =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `sample` numberOfTests

{-| Analog of `propertyN` for functions of four arguments
-}
property4N : Int -> String -> (a -> b -> c -> d -> Bool) -> Generator a -> Generator b -> Generator c -> Generator d -> Property
property4N numberOfTests name predicate generatorA generatorB generatorC generatorD =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `on` generatorD `sample` numberOfTests

{-| Analog of `propertyN` for functions of five arguments
-}
property5N : Int -> String -> (a -> b -> c -> d -> e -> Bool) -> Generator a -> Generator b -> Generator c -> Generator d -> Generator e -> Property
property5N numberOfTests name predicate generatorA generatorB generatorC generatorD generatorE =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `on` generatorD `on` generatorE `sample` numberOfTests



{-| Create a property given a name, a condition to test and a generator
Example :

    doubleNegativeIsPositive =
      property "Double Negative is Positive"
               (\number -> -(-number) == number)
               (float -300 400)
Note : This property will create 100 test cases. If you want a different
number, use `propertyN`
-}
property : String -> (a -> Bool) -> Generator a -> Property
property name predicate generator = 
  name `describedBy` predicate `on` generator

{-| Analog of `property` for functions of two arguments
Example :

    property2 "Bad Addition Subtraction Inverse"
              (\a b -> (a - b - 1) == (a + (-b)))
              (float 0 100) (float 0 100)
-}
property2 : String -> (a -> b -> Bool) -> Generator a -> Generator b -> Property
property2 name predicate generatorA generatorB =
  name `describedBy` predicate `on` generatorA `on` generatorB

{-| Analog of `property` for functions of three arguments
-}
property3 : String -> (a -> b -> c -> Bool) -> Generator a -> Generator b -> Generator c -> Property
property3 name predicate generatorA generatorB generatorC =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC

{-| Analog of `property` for functions of four arguments
-}
property4 : String -> (a -> b -> c -> d -> Bool) -> Generator a -> Generator b -> Generator c -> Generator d -> Property
property4 name predicate generatorA generatorB generatorC generatorD =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `on` generatorD

{-| Analog of `property` for functions of five arguments
-}
property5 : String -> (a -> b -> c -> d -> e -> Bool) -> Generator a -> Generator b -> Generator c -> Generator d -> Generator e -> Property
property5 name predicate generatorA generatorB generatorC generatorD generatorE =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `on` generatorD `on` generatorE

{-| Analog of `property` for functions of six arguments
-}
property6 : String -> (a -> b -> c -> d -> e -> f -> Bool) -> Generator a -> Generator b -> Generator c -> Generator d -> Generator e -> Generator f -> Property
property6 name predicate generatorA generatorB generatorC generatorD generatorE generatorF =
  name `describedBy` predicate `on` generatorA `on` generatorB `on` generatorC `on` generatorD `on` generatorE `on` generatorF


infixl 1 `describedBy`
infixl 0 `on`
infixl 0 `sample`

-- Some code from the examples that has to type check
axiom : Property
axiom = "5 equals 5" `describedBy` 5 == 5 

prop_identity : Property
prop_identity = "Identity" `describedBy` (\x -> x == identity x) `on` int 0 1000

prop_identity_n : Property
prop_identity_n = "Identity" `describedBy` (\x -> x == identity x) `on` int 0 1000 `sample` 200

{-| Constructs an initial PartiallyAppliedPredicate, binding some predicate as the 
unappliedRest and the seed with which generation of the TestResult began.
-}
partiallyAppliedPredicate : a -> Seed -> PartiallyAppliedPredicate a
partiallyAppliedPredicate predicate seed =
  { unappliedRest = predicate
  , revArguments = []
  , seed = seed
  }

{-| Function for building up a property starting with a name
and the actual code to check.

    axiom = "5 equals 5" `describedBy` 5 == 5 
-}
describedBy : String -> a -> PropertyBuilder a
describedBy name predicate = 
  { name = name
  , wrappedGenerator = 
      customGenerator
        (\seed ->
          (partiallyAppliedPredicate predicate seed, seed))
  , requestedSamples = Nothing
  }

{-| Further applies the wrapped property generator of an PartiallyAppliedPredicate
and saves the argument.
-}
applyToProperty : PartiallyAppliedPredicate (a -> b) -> a -> PartiallyAppliedPredicate b
applyToProperty p a =
  { p | unappliedRest <- p.unappliedRest a, revArguments <- toString a :: p.revArguments }

{-| Supplies generators for arguments of the property to build up. 
Using an infix operator like this, we can support functions with an
arbitrary number of arguments.

    prop_identity = "Identity" `describedBy` (\x -> x == identity x) `on` int 0 1000
-}
on : PropertyBuilder (a -> b) -> Generator a -> PropertyBuilder b
on builder generatorA =
  { builder 
  | wrappedGenerator <- customGenerator
    (\seed ->
      let (ip, seed') = generate builder.wrappedGenerator seed
          (a, seed'') = generate generatorA seed'
          ip' = applyToProperty ip a
      in (ip', seed''))
  }

{-| Dictate how many samples to generate for the property.

    prop_identity_n = "Identity" `describedBy` (\x -> x == identity x) `on` int 0 1000 `sample` 200
-}
sample : PropertyBuilder a -> Int -> PropertyBuilder a
sample builder n =
  { builder
  | requestedSamples <- Just n
  }

defaultNumberOfSamples : Int
defaultNumberOfSamples = 100

{-| The `PartiallyAppliedPredicate` is now fully applied, so we expect `unappliedRest` to evaluate to
a boolean, indicating whether this particular test succeeded.
We take name, value and seed directly from the `PartiallyAppliedPredicate`.
-}
toResult : String -> PartiallyAppliedPredicate Bool -> TestResult
toResult name ip = 
  { name = name
  , failed = not (ip.unappliedRest)
  , value = ip.revArguments |> reverse |> join ", "
  , seed = ip.seed
  }

propertyResults : Property -> Generator (List TestResult)
propertyResults p = 
  list -- generate p.requestedSamples from the property, with the result turned into a TestResult
    (withDefault defaultNumberOfSamples p.requestedSamples) -- number of samples to generate
    (rMap (toResult p.name) p.wrappedGenerator) -- converts each generated PartiallyAppliedPredicate into a TestResult


mergeTestOutputsWith : (List TestResult -> List TestResult -> List TestResult) -> TestOutput -> TestOutput -> TestOutput
mergeTestOutputsWith resultMerger output1 output2 =
  let u = Dict.union output1 output2     -- We only need to correct intersections
      i = Dict.intersect output2 output1 -- Note that we give preference to output2
                                         -- Now we need to append every bucket in i 
                                         -- to its bucket in u.
      unsafeGet key dict =
        case Dict.get key dict of
          Just v -> v
          Nothing -> Debug.crash "unsafeGet with a not-found key" -- Cannot happen actually
      mergeBuckets key output =
        let results = resultMerger (unsafeGet key u) (unsafeGet key i)
        in Dict.insert key results output 
  in foldl mergeBuckets u (Dict.keys i)


mergePreferringFailures : List TestResult -> List TestResult -> List TestResult
mergePreferringFailures ys xs = -- ys are the fresh results, xs the accumulated
  let failures = filter .failed ys ++ filter .failed xs
  in if length failures == 0
     then ys
     else failures


{-| Check a list of properties given a random seed.
Checks each property with the same initial seed, so 
reversing order of properties is OK for reproducing bugs.

    check
      [ prop_reverseReverseList
      , prop_numberIsOdd
      , prop_numberIsEqualToItself
      ]
      (initialSeed 1)
-}
check : List Property -> Seed -> TestOutput
check properties seed = 
    let eval p = (p.name, fst <| generate (propertyResults p) seed)
    in properties |> map eval |> Dict.fromList

{-| Version of check with a default initialSeed of 1
-}
simpleCheck : List Property -> TestOutput
simpleCheck properties =
  check properties (initialSeed 1)

{-| Version of check which continuously runs every second
and uses the current time as its seed and merges test outputs.
-}
continuousCheck : List Property -> Signal TestOutput
continuousCheck =
  continuousCheckEvery second


{-| Version of check which continuously runs every given time interval
and uses the current time as its seed and merges test outputs.

    continuousCheck = continuousCheckEvery second
-}
continuousCheckEvery : Time -> List Property -> Signal TestOutput
continuousCheckEvery time properties =
  Signal.foldp (mergeTestOutputsWith mergePreferringFailures) Dict.empty
    (Signal.map ((check properties) << initialSeed << round) (every time))


{-| Version of check which continuously runs every second
and uses the current time as its seed and accumulates all test outputs.
-}
deepContinuousCheck : List Property -> Signal TestOutput
deepContinuousCheck =
  deepContinuousCheckEvery second


{-| Version of check which continuously runs every given time interval
and uses the current time as its seed and accumulates all test outputs.
-}
deepContinuousCheckEvery : Time -> List Property -> Signal TestOutput
deepContinuousCheckEvery time properties =
  Signal.foldp (mergeTestOutputsWith (++)) Dict.empty
    (Signal.map ((check properties) << initialSeed << round) (every time))


printResultWith : (List String -> String) -> (String, List TestResult) -> String
printResultWith flattener (name, results) =
  let failures = filter .failed results
  in
    if length failures == 0
    then name ++ " has passed " ++ toString (length results) ++ " tests!"
    else
      (flattener
        (map
          (\r ->
              if r.failed 
              then r.name ++ " has failed with the following input: " ++ r.value
              else r.name ++ " has passed with the following input: " ++ r.value)
          failures))

printSingleResult : (String, List TestResult) -> String
printSingleResult = printResultWith head

printManyResults : (String, List TestResult) -> String
printManyResults = printResultWith (join "\n")

{-| Print a test output as a string.
-}
print : TestOutput -> String
print output =
  output |> Dict.toList |> map printSingleResult |> join "\n"

{-| Print a test output as a detailed string.
-}
printVerbose : TestOutput -> String
printVerbose output =
  output |> Dict.toList |> map printManyResults |> join "\n"

{-| Display a test output as an Element.
Useful for viewing in the browser.
-}
display : TestOutput -> Element
display output =
  let outputString = print output
  in
    leftAligned (monospace (fromString outputString))

{-| Display a detailed test output as an Element.
Useful for viewing in the browser.
-}
displayVerbose : TestOutput -> Element
displayVerbose output =
  let outputString = printVerbose output
  in
    leftAligned (monospace (fromString outputString))


------ From elm-random-extra -------
--- The following functions are copied from elm-random-extra
--- In order to not depend explicity on elm-random-extra
--- Hopefully, these functions will be merged with the core random module

rMap : (a -> b) -> Generator a -> Generator b
rMap f generator =
  customGenerator
    (\seed ->
        let (value, nextSeed) = generate generator seed
        in
          (f value, nextSeed))