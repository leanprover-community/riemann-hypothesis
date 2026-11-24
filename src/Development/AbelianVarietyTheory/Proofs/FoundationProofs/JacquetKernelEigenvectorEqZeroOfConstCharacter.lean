module

public import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeConstantFamilyDetCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SphericalVectorNotInBorelJacquetKernelStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem eq_zero_of_isEig_const : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsSmooth π → IsSmoothChar χ → ∀ v ∈ twKer π (unipB k (Fin n)) 1, IsEig π (grp fun _ => χ) (theta fun _ => χ) v → v = 0 := by
  intro k _ _ _ _ n χ V _ _ π hπ hχ v hv he
  obtain ⟨h1, h2⟩ := GlobalTheory.T.principalSeriesType_constant_family_det_character k n χ
  have hs : IsSmoothChar (detChar (Fin n) χ)⁻¹ := by
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin n) k → kˣ) :=
      Matrix.GeneralLinearGroup.continuous_det
    have ho : IsOpen ((χ.ker : Set kˣ)) := hχ
    have := ho.preimage hc
    unfold IsSmoothChar
    convert this using 1
    ext g
    simp [detChar, MonoidHom.mem_ker]
  have hk : twKer (twist π (detChar (Fin n) χ)⁻¹) (unipB k (Fin n)) 1 = twKer π (unipB k (Fin n)) 1 := by
    unfold twKer
    congr 1
    ext w
    refine exists_congr fun u => exists_congr fun x => ?_
    have hd : Matrix.GeneralLinearGroup.det (u : GL (Fin n) k) = 1 := det_eq_one_of_mem_unipRad k u.2
    have : twist π (detChar (Fin n) χ)⁻¹ (u : GL (Fin n) k) x = π (u : GL (Fin n) k) x := by
      simp [twist, detChar, hd]
    rw [this]
  refine GlobalTheory.T.spherical_vector_not_in_borel_jacquet_kernel k n V (twist π (detChar (Fin n) χ)⁻¹) (isSmooth_twist hπ hs) v (hk ▸ hv) ?_
  intro g hg
  have h3 := he g (by rw [h1]; exact hg)
  rw [h2 g hg] at h3
  show (((detChar (Fin n) χ)⁻¹ g : ℂˣ) : ℂ) • π g v = v
  rw [h3, smul_smul]
  simp

end GlobalTheory.PsType
