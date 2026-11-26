module

public import New.Spanning.SecondMoment.HilbertSchmidt
public import New.Spanning.SecondMoment.PositiveType

/-!
# Few translates fill

Compatibility entry point for callers using the original module name. The second-moment
and greedy-spanning declarations now live in `HilbertSchmidt` and `Spread`; new callers should
import the module that contains the result they use.
-/
