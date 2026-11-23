module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace Formalism.L2

variable {l : ℕ} [Fact l.Prime]

structure ArithTied (P : LocPrime l) : Prop where
  val : ∀ (LL : FinExt l) (x : ↥LL.1) (q : ℚ),
    P.v LL x = ((q : ℚ) : WithTop ℚ) ↔ ‖((x : ↥LL.1) : Om l)‖ = (l : ℝ) ^ (-(q : ℝ))

def BridgeInd {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (A : ValuationSubring Ω) : Prop :=
  ∀ x : Ω, x ∈ A ↔ ‖Bw.j x‖ ≤ 1

def vrep {K LL : FinExt l} {m : ℕ} (r : ↥(GK K) →* GL (Fin m) ↥LL.1) :
    Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r)

structure LocTied (D : D7) where
  arith : ∀ (l : ℕ) [Fact l.Prime], ArithTied (D.loc l)

  nbr : ∀ (i : D.nd.Loc) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    BridgeInd (D.nbr i w hw) (D.nd.plOm.1 w)
  ntwbr : ∀ (i : D.ntw.Tw) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.ntw.l i)),
    BridgeInd (D.ntwbr i w hw) (D.nd.plOm.1 w)

end Formalism.L2
