module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Formalism.LocalToGlobal.Columns.RecLevel
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceProjectionZeroIntegralIffComponentsAbove
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.Col2.AdSupport

theorem adAt_entry_eq_one_of_not_over {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (z : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hz : ∀ v', v' ≠ v → bc (prV (E := E) v') z = 1) (P : HeightOneSpectrum (𝓞 E)) (hP : ¬ Formalism.L2.Col.IsOver v P)
    (r s : Fin n) :
    adAt F P ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
  have hne : P.under (𝓞 F) ≠ v := by
    intro h
    apply hP
    rw [← h]
    rfl
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F) =>
    (g : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s) (hz _ hne)
  have h3 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] (P.under (𝓞 F)).adicCompletion F)) r s := h2
  have h4 : prV (E := E) (P.under (𝓞 F)) ((z : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) r s) = 0 := by
    rw [map_sub, h3, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h5 := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E (P.under (𝓞 F)) _).1.1 h4) P rfl
  rw [map_sub, sub_eq_zero] at h5
  rw [h5, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdSupport
