module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private noncomputable def repOf {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V :=
  AlgHom.ofLinearMap
    { toFun := fun x => β.symm.toLinearMap ∘ₗ (x.mulVecLin.restrictScalars ℚ) ∘ₗ β.toLinearMap
      map_add' := fun x y => by
        ext v
        simp [Matrix.add_mulVec]
      map_smul' := fun c x => by
        ext v
        simp [Matrix.smul_mulVec] }
    (by ext v; simp)
    (fun x y => by ext v; simp [Matrix.mulVec_mulVec])

private theorem repOf_apply {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) (x : Matrix (Fin n) (Fin n) E) (z : V) : β (repOf β x z) = x *ᵥ β z := by
  simp [repOf]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pSetupEx :
    FormOKSt → FormPerfSt → SigSt → DomSt → AtPEx → RepEx → RepLaws → RepAdj → Orient → SetupEx := by
  intro hF hFP hS hD hP hR hL hA hO E _ _ _ A n p _ hn hg
  have facts : A.Facts n := ⟨hn, hF E A n, hD E A n hn⟩
  have hs : A.SigOK n := hS E A n hn
  have perf : A.FormPerf n p := hFP E A n p hg.2
  obtain ⟨P⟩ := hP E A p hg.1
  obtain ⟨β, hβ⟩ := hR E n
  have hok : RepOK A n (repOf β) := ⟨β, hβ, repOf_apply β⟩
  obtain ⟨r1, r2, r3, r4⟩ := hL E A n (repOf β) hok
  have radj := hA E A n (repOf β) hok
  obtain ⟨J, j1, j2, j3, j4⟩ := hO E A n hn hs p P (repOf β) hok
  have hsig : ∀ v : InfinitePlace E, sigPos (A.herm n) v.embedding = 1 ↔
      ∃ _ : Fin 1, v = InfinitePlace.mk (P.iotaC.comp P.s) := fun v => by
    have hv := hs v.embedding
    rw [InfinitePlace.mk_embedding] at hv
    have hc : P.iotaC.comp P.s = A.τ₀ := RingHom.ext P.s_C
    rw [hc]
    constructor
    · intro h
      by_cases hv0 : v = InfinitePlace.mk A.τ₀
      · exact ⟨0, hv0⟩
      · have h0 := (hv.2 hv0).1
        omega
    · rintro ⟨_, h⟩
      exact (hv.1 h).1
  refine ⟨⟨facts, hs, hg, perf, P, ?_, ?_, ?_⟩⟩
  · exact
      { e := RingEquiv.refl E
        n_eq := rfl
        rep := repOf β
        rep_inj := r1
        rep_range := r2
        rep_F := fun c => r3 c
        adj := radj
        ρp := P.ρp
        ρp_eq := P.ρp_eq
        s := fun _ => P.s
        s_C := fun _ x => P.s_C x
        w := fun _ => P.w
        s_P := fun _ x => P.s_P x
        sig := hsig
        orient := ⟨J, j1, j2, j3, j4⟩ }
  · intro x; rfl
  · exact r4
