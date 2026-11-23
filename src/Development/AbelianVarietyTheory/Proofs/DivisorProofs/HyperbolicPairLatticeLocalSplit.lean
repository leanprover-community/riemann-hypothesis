module

public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabiliserSplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionSplitPlace
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.IwSplitLine

theorem iwasawa_line_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  obtain ⟨P, P', hne, hP, hP'⟩ := hv
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (v := v) hne (IsDedekindDomain.HeightOneSpectrum.ext hP) (IsDedekindDomain.HeightOneSpectrum.ext hP')
  obtain ⟨k, i, qq, hn, hsum⟩ := GlobalTheory.IwSplitFrame.exists_compl x y (cT (σ : E →+* E) y * J) (cT (σ : E →+* E) x * J)
    hyx hyy hxx hxy
  obtain ⟨B, lv, hB⟩ := GlobalTheory.Core.Rk.IwFlagSplit.exists_flag_basis (v := v) τ hJ
    (e := x) (e' := y) (i := i) (p := cT (σ : E →+* E) y * J) (q := qq)
    (Fintype.equivOfCardEq (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)) hsum hxy
  have hQ : ∀ z : GLoc σ J v, (B⁻¹ * splitHom σ J τ z * B).1.BlockTriangular lv →
      z ∈ GlobalTheory.IwSplitFrame.keepGrp (σ := σ) (J := J) (v := v) (x.map (inclR (F := F) (Fv F v))) :=
    fun z hz => by
      obtain ⟨⟨b, hb⟩, b', hb'⟩ := hB z hz
      exact GlobalTheory.IwSplitFrame.keeps_of_split h τ z hyx hb hb'
  obtain ⟨q, k', hq, hk, rfl⟩ := GlobalTheory.Core.Rk.IwFlagSplit.iwasawa_of_triangular h hJ τ L hL _ B lv hQ g
  obtain ⟨β, hβ⟩ := hq
  exact ⟨q, k', hk, rfl, β, hβ⟩

end GlobalTheory.IwSplitLine
