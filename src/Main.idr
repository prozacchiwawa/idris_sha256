import Data.Vect
import Data.Bin
import Numbers
import Sha256

main : IO ()
main =
  let
    input : Vect 4 Integer
    input = Vect.fromList [ 65, 66, 67, 10 ]

    result : Vect 32 Bin
    result = sha256 input
  in
  putStrLn $ show result
