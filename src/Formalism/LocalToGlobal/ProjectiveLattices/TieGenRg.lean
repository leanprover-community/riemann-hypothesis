module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompData
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Formalism.LocalRingCardinality.Params
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem ratio_single {Z : Comp Xo c} (G : WTZ E) (r s : Om Z) (hs : s ≠ 0) :
    ratio (Ω := Om Z) (AddMonoidAlgebra.single G r : AC Z) (AddMonoidAlgebra.single G s) = r / s := by
  have hex : ∃ a : Om Z, (AddMonoidAlgebra.single G r : AC Z) = a • AddMonoidAlgebra.single G s :=
    ⟨r / s, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ r hs]⟩
  unfold ratio
  rw [dite_eq_left hex]
  have e := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at e
  have e2 : r = hex.choose * s := by
    simpa [AddMonoidAlgebra.coeff_single] using congrArg (fun q : AC Z => q.coeff G) e
  rw [eq_div_iff hs]
  exact e2.symm

variable {D : D7} {T : Top D} {j : ℕ}
  {d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)}
  {Z : Comp (T.Q.Xo j) T.Q.c} {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r}


end Formalism.L2.Pj
