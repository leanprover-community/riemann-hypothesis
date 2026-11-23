module

public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.CompanionTheory.Ar.Lines

open NumberField TensorProduct GroundTheory.Heights₂.Heights Matrix
open scoped ComplexOrder nonZeroDivisors

noncomputable section

theorem gramAt_standard {L : Type} [Field L] {i : ℕ} (h : Matrix (Fin i) (Fin i) ℂ) (σ : L →+* ℂ) :
    gramAt h σ (fun j : Fin i => (Pi.single j 1 : Fin i → L)) = h := by
  have he : ∀ j : Fin i, embVec σ (Pi.single j 1 : Fin i → L) = Pi.single j 1 := by
    intro j
    funext k
    by_cases hk : k = j
    · subst hk; simp [embVec]
    · simp [embVec, Pi.single_eq_of_ne hk]
  ext a b
  simp [gramAt, he, Matrix.mulVec_single_one, Matrix.col_apply]

theorem degree_eq_degreeWith (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L))
    (Fl : HermLattice L i) (hf : LinearIndependent (𝓞 L) f) (hi : i = B.rank F)
    (hc : Function.Injective c) (hcf : ∀ j, c (f j) = Pi.single j 1)
    (hlat : Fl.lattice = LinearMap.range c)
    (hmet : ∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) :
    Fl.degree = B.degreeWith F f := by
  have hspanK : Submodule.span L (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) = ⊤ := by
    have h : (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) =
        Set.range (Pi.basisFun L (Fin i)) := by
      congr 1; funext j; exact (Pi.basisFun_apply _ _ _).symm
    rw [h]
    exact (Pi.basisFun L (Fin i)).span_eq
  have hS : (Submodule.span (𝓞 L) (Set.range f)).map c =
      Submodule.span (𝓞 L) (Set.range fun j : Fin i => (Pi.single j 1 : Fin i → L)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    exact congrArg _ (congrArg Set.range (funext hcf))
  have hA : (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
      (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)) = LinearMap.range c := by
    rw [hspanK, hlat, Submodule.restrictScalars_top, inf_top_eq]
  have hidx : genIndex
      (Fl.lattice ⊓ (Submodule.span L (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).restrictScalars (𝓞 L)).toAddSubgroup
      (Submodule.span (𝓞 L) (Set.range fun j : Fin i =>
        (Pi.single j 1 : Fin i → L))).toAddSubgroup =
      (Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range f)) : ℝ) := by
    rw [hA, ← hS, genIndex]
    have hle : ((Submodule.span (𝓞 L) (Set.range f)).map c).toAddSubgroup ≤
        (LinearMap.range c).toAddSubgroup := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    rw [AddSubgroup.relIndex_eq_one.mpr hle, LinearMap.range_eq_map, Submodule.map_toAddSubgroup,
      Submodule.map_toAddSubgroup, AddSubgroup.relIndex_map_map_of_injective _ _ hc,
      Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    simp
    rfl
  have hgram : ∀ σ : L →+* ℂ,
      (gramAt (Fl.metric σ) σ fun j : Fin i => (Pi.single j 1 : Fin i → L)).det.re =
        ‖HermitianBundle.gramDet B σ (fun j => (f j : B.carrier))‖ := by
    intro σ
    have hd : HermitianBundle.gramDet B σ (fun j => (f j : B.carrier)) = (Fl.metric σ).det := by
      rw [hmet σ]
      rfl
    rw [gramAt_standard, hd]
    have hp : 0 < (Fl.metric σ).det := (Fl.posDef σ).det_pos
    have hre : ((Fl.metric σ).det.re : ℂ) = (Fl.metric σ).det := by
      apply Complex.ext
      · simp
      · simpa using (Complex.lt_def.mp hp).2.symm ▸ rfl
    rw [← hre, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    exact (Complex.lt_def.mp hp).1
  simp only [HermLattice.degree, subDegree, HermitianBundle.degreeWith, hidx, hgram]

end

end GlobalTheory.CompanionTheory.Ar.Lines
