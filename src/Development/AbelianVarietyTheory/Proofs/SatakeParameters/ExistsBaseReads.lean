module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem exists_base_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (ι : Om l ≃+* ℂ) (τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g₀ : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ₀.toRingHom.comp c)) = H.emb g₀ → ∃ κ : H.E →+* ↥LL.1, ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : R.GG), ι.toRingHom.comp (LL.1.val.toRingHom.comp (τ.toRingHom.comp c)) = H.emb g → Reads H c κ τ g := by
  intro R H l _ K LL c ι τ₀ g₀ h₀
  refine ⟨τ₀.toRingHom.comp (c.comp ((H.sigmaOf g₀).symm : H.E →+* H.E)), ?_⟩
  intro τ g hτ x
  have hinj : Function.Injective (fun y : ↥LL.1 => ι (LL.1.val y)) :=
    ι.injective.comp (LL.1.val.injective)
  apply hinj
  have e1 := DFunLike.congr_fun hτ x
  have e2 := DFunLike.congr_fun h₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x))
  simp only [RingHom.comp_apply] at e1 e2
  simp only [RingHom.comp_apply]
  change ι (LL.1.val (τ (c x))) = ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x)))))
  have e1' : ι (LL.1.val (τ (c x))) = H.emb g x := e1
  have e2' : ι (LL.1.val (τ₀ (c ((H.sigmaOf g₀).symm (H.sigmaOf g x))))) = H.emb g₀ ((H.sigmaOf g₀).symm (H.sigmaOf g x)) := e2
  rw [e1', e2']
  simp [Host.emb]

end GlobalTheory.HTW.Rec
