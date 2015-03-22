import Text (plainText)
import Random (..)
import Check (..)
import Signal (..)
import List

prop_numberIsIdentity : Property
prop_numberIsIdentity = propertyN 100 "number is identity" (\n -> n == n) (int 0 100)

prop_numberIsOdd : Property
prop_numberIsOdd = property "number is odd" (\n -> n % 2 == 1) (int 0 100)

prop_reverseReverseList : Property
prop_reverseReverseList =
  property "reverse reverse list" (\l -> List.reverse (List.reverse l) == l) (list 100 (int 0 100))

prop_discontinuous : Property
prop_discontinuous =
  property "discontinuous" (\x -> (x - 1) // (x - 1) == 1) (int 0 1000)

prop_numberIsEven : Property
prop_numberIsEven =
  "number is even, 0 samples" `describedBy` (\n -> n % 2 == 0) `on` int 0 100 `sample` 0

-- Now some pretty infix operators, just to show that it's possible.
-- You can define your own operators of course, these are just what I
-- came up with in one minute:
(<:) = describedBy
(<@) = on -- The duck head operator
(<#>) = sample

prop_01Identity : Property
prop_01Identity =
  "0-1 is identity on two inputs" <: (\a b -> a == b) <@ int 0 1 <@ int 0 1 <#> 2


test : Signal TestOutput
test =
  continuousCheck
    [ prop_numberIsIdentity
    , prop_discontinuous
    , prop_numberIsOdd
    , prop_reverseReverseList
    , prop_numberIsEven
    , prop_01Identity
    ]


main =
  display <~ test
