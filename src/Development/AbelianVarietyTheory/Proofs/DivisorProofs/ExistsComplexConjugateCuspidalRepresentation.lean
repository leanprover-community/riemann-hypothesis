module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliOperatorAlgebraStableUnderComplexConjStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOfConjPointwise
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAdelicGLComplexConjCommutesOperatorsStatement
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory

def CuspRep.CuspSub.mapConj {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (π : CuspSub E a) (C : Sm E a ≃ₗ⋆[ℂ] Sm E a) (hact : ∀ o φ, act o (C φ) = C (act o φ))
    (hcusp : ∀ φ : Sm E a, IsCuspForm φ → IsCuspForm (C φ)) : CuspSub E a where
  V := π.V.map C.toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact hcusp φ (π.cusp φ hφ)
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable o φ hφ, (hact o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := C)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap C.toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← C.injective h2]) fun o φ hφ => by
      change C (act o φ) ∈ W
      rw [← hact]
      exact hs o _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := C.toLinearMap) C.surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

theorem exists_conj_cuspSub : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a),
    ∃ (π' : CuspSub E a) (J : π.V ≃ₗ⋆[ℂ] π'.V), ∀ o φ, J (π.op o φ) = π'.op o (J φ) := by
  intro E _ _ _ a π
  obtain ⟨C, hC, hact⟩ := GlobalTheory.T.smooth_adelic_GL_complex_conj_commutes_operators E a
  have hZ := GlobalTheory.T.capelli_operator_algebra_stable_under_complex_conj E a C hact
  have hcusp := isCuspForm_of_conj_pointwise E a C hC hact hZ
  refine ⟨π.mapConj C hact hcusp, C.submoduleMap π.V, fun o φ => Subtype.ext ?_⟩
  exact (hact o φ.1).symm

end GlobalTheory
