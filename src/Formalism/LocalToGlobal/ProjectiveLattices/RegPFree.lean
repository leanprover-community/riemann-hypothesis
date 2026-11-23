module

public import Formalism.LocalToGlobal.ProjectiveLattices.PtFree
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.RegLaw
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
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

@[expose] public section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (io : c.F →+* T.Fr) (_y : IntFr Xo c T io) : Prop := True

theorem valSet_alg_subset (la : HeightOneSpectrum (𝓞 c.F)) :
    valSet Xo c (algCls Xo c) la ⊆ valSet Xo c (trivialClassCondition Xo c) la := by
  rintro _ ⟨y, rfl⟩
  exact ⟨PtV.widen (fun _ _ _ _ => trivial) y, rfl⟩

def trivSet : Set (Rul Xo c → EReal) :=
  {q | ∃ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io),
    (∀ a : c.F, a ≠ 0 → vV T.V (io a) = 0) ∧ q = fun f => nval T.V 1 (evI y f)}

def NoCommonZero {n : ℕ} (ws : Fin n → Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), ∃ i, evR Xo c (ws i) y ≠ 0

abbrev DomWt (E : Type) [Field E] : Type := {x : ((E →+* ℂ) × ℕ → ℕ) × ℕ // Dom x.1 x.2}

def regular₂ {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Prop :=
  ReciprocityTheory.ChartRestriction.G.T0.RegLaw (Λ := HeightOneSpectrum (𝓞 c.F)) (Wt := DomWt E)
    (fun w => cusp Xo c U w.1.1 w.1.2)
    (fun la => valSet Xo c (algCls Xo c) la) (fun la => valSet Xo c (trivialClassCondition Xo c) la)
    (fun la v => ⟨v.1, valSet_alg_subset Xo c la v.2⟩) (fun _ v _ F => v.1 F.1)
    (trivSet Xo c) (fun q _ F => q.1 F.1) (fun ws => NoCommonZero Xo c fun i => (ws i).1) ∧
  ∀ a n, Dom a n → ∀ (m : ℕ) (ws : Fin m → Rul Xo c), (∀ i, ws i ∈ cusp Xo c U a n) → NoCommonZero Xo c ws →
    ∀ nu : HeightOneSpectrum (𝓞 c.F) → ℝ,
      (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)) →
        ∀ la, ∀ v ∈ valSet Xo c (trivialClassCondition Xo c) la, (⨅ i, v (ws i)) ≤ (nu la : EReal)

variable {Xo c}

end Formalism.L2.PjFree
