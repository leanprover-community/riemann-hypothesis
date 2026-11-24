module

public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
public import Formalism.LocalToGlobal.ProjectiveLattices.LiesOverBaseChange
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def NabUniq : Prop :=
  ∀ (_ : StarRing (𝓞 E)) (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ a n, Dom a n → thGen Xo c nab a n = thGen Xo c nab' a n

def DatIndep : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (Tw Tw' : PointsOfFlagModel.Tower (WeightAlgebra.resCh la) Xo c), PointsOfFlagModel.TowerAt Tw → PointsOfFlagModel.TowerAt Tw' →
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io), OverLa la T.V io e → algCls Xo c T io y →
      ∀ z z', LiesOverBaseChange la Tw T io y z → LiesOverBaseChange la Tw' T io y z' →
        ∀ (A : DatAt (Tw.Y z.1) z.2.2.1) (A' : DatAt (Tw'.Y z'.1) z'.2.2.1),
          ∃ f : A.Ylat ≃ₗ[𝓞 E] A'.Ylat, ∀ a b, A'.beta (f a) (f b) = A.beta a b

end Formalism.L2.Pj
