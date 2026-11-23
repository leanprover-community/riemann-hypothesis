module

public import Development.EtaleCohomology.WeilConjectures.AbsorbPf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

noncomputable section
open CategoryTheory LateralTheory.E.t_E3Cut TensorProduct

namespace LateralTheory.EWeil.AbsorbPf2

theorem etaleNeighborhoods_have_common_refinement : LateralTheory.EWeil.AbsorbPf.Pair := by
  intro A B C Ω _ ι gB gC hB hC φB φC hφB hφC
  letI := gB.hom.toAlgebra
  letI := gC.hom.toAlgebra
  letI := ι.toAlgebra
  haveI : Algebra.Etale A B := (RingHom.etale_algebraMap (R := A) (S := B)).mp hB
  haveI : Algebra.Etale A C := (RingHom.etale_algebraMap (R := A) (S := C)).mp hC
  let φB' : B →ₐ[A] Ω := { φB with commutes' := fun a => RingHom.congr_fun hφB a }
  let φC' : C →ₐ[A] Ω := { φC with commutes' := fun a => RingHom.congr_fun hφC a }
  let L := Algebra.TensorProduct.lift φB' φC' (fun _ _ => Commute.all _ _)
  refine ⟨CommRingCat.of (B ⊗[A] C), CommRingCat.ofHom (algebraMap A (B ⊗[A] C)), L.toRingHom,
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom,
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := B) (B := C)).toRingHom,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · haveI : Algebra.Etale B (B ⊗[A] C) := inferInstance
    haveI : Algebra.Etale A (B ⊗[A] C) := Algebra.Etale.comp A B (B ⊗[A] C)
    exact (RingHom.etale_algebraMap (R := A) (S := B ⊗[A] C)).mpr inferInstance
  · ext a; exact L.commutes a
  · ext a
    show (gB.hom a) ⊗ₜ[A] (1 : C) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]; rfl
  · ext a
    show (1 : B) ⊗ₜ[A] (gC.hom a) = algebraMap A (B ⊗[A] C) a
    rw [Algebra.TensorProduct.algebraMap_apply]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := A) (A := B) (B := C) a).symm
  · ext b
    show L (b ⊗ₜ 1) = φB b
    simp [L, φB']
  · ext c
    show L (1 ⊗ₜ c) = φC c
    simp [L, φC']

end LateralTheory.EWeil.AbsorbPf2
