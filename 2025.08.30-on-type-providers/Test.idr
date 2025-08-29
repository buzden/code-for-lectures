import MicroJsonSchema

-- All this code can be present in the `MicroJsonSchema` module, but here we also test that this module exports enough

%default total
%language ElabReflection

Example = %runElab deriveJsonSchema $ File "example.json"

Example2 = %runElab deriveJsonSchema $ File "example2.json"

someExample : Example
someExample = MkExample { names = ["Denis", "Buzdalov"], age = 35, email = "test@example.com" }

accessAll = (someExample.names, someExample.age, someExample.email)
accessCorr = the (someExample.age = 35) Refl

someExample2 : Example2
someExample2 = MkExample2 ["Denis", "Buzdalov"] 35 "test@example.com"

domainName : Example2 -> String
domainName $ MkExample2 {email, _} = matchWholeResult Example2.emailRegex email |> \[domain] => domain

Example3 = %runElab deriveJsonSchema $ File "example3.json"

someExample3 : Example3
someExample3 = MkExample3 "Denis Buzdalov" (MkAge 15)
