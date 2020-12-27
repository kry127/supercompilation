## Tasks to implement in SC

### Roadmap
#### pt. 1 -- basic
-[x] Tree program representation
-[x] Tree pretty-printer
-[x] Interpreter
-[x] **Tests**

#### pt. 2 -- expressions operation and relations
-[x] Tightest expression generalization (e1 ⨅ e2)
-[ ] Homeomorphic inception relation (**◁**, **⊴**)
-[ ] **Tests**
```(\x.x x)(\x.x x) <=> f f where f = \x.x x```

#### pt. 3 -- tree operations
-[ ] Driving
-[ ] Whistle(b, ◁) (a.k.a. _find_)
  > find ancestor node a such that a ◁ b
-[ ] Folding (if expr is renaming, make backtrace arc)
-[ ] Let-abstraction generalization
-[ ] **Tests**

### Optional
-[ ] Lambda-lifting preprocessing (move lambdas to `where` block and name them)
-[ ] Tree parser
-[ ] CLI
-[ ] KMP Test


### Program example
```
sum (squares (upto 1 n)) 0
 where
  sum     = \xs . \a .
          case xs of
          []     -> a
          x : xs -> x + sum xs a
          esac
          
  squares = \xs.
          case xs of
          []     -> []
          x : xs -> (x * x) : squares xs
          esac
          
  upto   = \m. \n.
          case (m > n) of
          True -> []
          False -> m : (upto (m + 1) n)
          esac
```