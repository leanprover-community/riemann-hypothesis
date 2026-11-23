module

public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
public import Formalism.LocalToGlobal.Columns.AdjointFrobeniusPreservesRamified
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV

section L3

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem mem_localization_of_smul_mem'₂ (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) {s : 𝓞 E}
    (hs : s ∉ P.asIdeal) {w : Sp E n} (h : s • w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N) : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N := by
  obtain ⟨s', hs', h'⟩ := (mem_locP P N _).1 h
  refine (mem_locP P N w).2 ⟨s' * s, fun hm => (P.isPrime.mem_or_mem hm).elim hs' hs, ?_⟩
  rwa [mul_smul]

theorem frame_exists (P : HeightOneSpectrum (𝓞 E)) {N : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsFullLattice E N) :
    ∃ f : Sp E n ≃ₗ[E] Sp E n, ∀ z, f z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N ↔ z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (stdLat E n) := by
  obtain ⟨β, hβN, hβI⟩ := exists_locBasis P hN
  refine ⟨β.equivFun.symm, fun z => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [mem_localization_standardLattice]
    intro i
    have := hβI _ h i
    rwa [Module.Basis.equivFun_symm_apply, Module.Basis.repr_sum_self] at this
  · rw [mem_localization_standardLattice] at h
    rw [Module.Basis.equivFun_symm_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, s, hs, hrs⟩ := h i
    apply mem_localization_of_smul_mem'₂ P N hs
    have e : s • (z i • β i) = r • β i := by
      rw [← algebraMap_smul E s, ← algebraMap_smul E r, smul_smul, hrs]
    rw [e]
    exact Submodule.smul_mem _ r (hβN i)

end L3


variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}



variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}



variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}



variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}


end DetChrL

end Formalism.L2.Col
