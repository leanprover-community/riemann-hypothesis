module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.MatIrrIff
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.irrOpenDet :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (H : Subgroup G),
    ∃ U : Set (PrimeSpectrum A), IsOpen U ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (p : PrimeSpectrum A),
        p.asIdeal = RingHom.ker φ → D.map φ = GDet.ofRep ρ → (p ∈ U ↔ U3.MatIrr H ρ) := by
  intro n A G _ _ D H
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨Set.univ, isOpen_univ, ?_⟩
    intro K _ _ φ ρ p _ _
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    exact ⟨fun _ => Subsingleton.elim _ _, fun _ => Set.mem_univ _⟩
  · obtain ⟨U, hU, h⟩ := UpperTheory.V.AlgebraTools.Det.irrOpen (ι := Fin n)
      (fun h : H => D.tr (MonoidAlgebra.single (h : G) 1))
    refine ⟨U, hU, ?_⟩
    intro K _ _ φ ρ p hp hD
    rw [UpperTheory.V.AlgebraTools.Det.matIrrIff H ρ]
    refine h K φ (ρ.comp H.subtype) p hp ?_
    intro g
    have hmap : (D.map φ).chi (MonoidAlgebra.single (g : G) 1) =
        (D.chi (MonoidAlgebra.single (g : G) 1)).map φ := by
      let : Algebra A K[X] := ((algebraMap K K[X]).comp φ).toAlgebra
      let f : A[X] →ₐ[A] K[X] :=
        { Polynomial.mapRingHom φ with
          commutes' := fun a => by
            change Polynomial.mapRingHom φ (algebraMap A A[X] a) = algebraMap K K[X] (φ a)
            simp [Polynomial.algebraMap_eq] }
      change D.D K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1)) = f (D.chi _)
      rw [GDet.chi, ← D.nat A[X] K[X] f]
      congr 1
      simp [f]
    have hrep : (GDet.ofRep ρ).chi (MonoidAlgebra.single (g : G) 1) = (ρ g).charpoly := by
      change (GDet.repAlg ρ K[X] (MonoidAlgebra.single 1 X -
        MonoidAlgebra.mapRingHom G C (MonoidAlgebra.single (g : G) 1))).det = _
      rw [map_sub, MonoidAlgebra.mapRingHom_single, map_one, Matrix.charpoly]
      simp only [GDet.repAlg, MonoidAlgebra.lift_single, MonoidHom.comp_apply,
        map_one, one_smul, Polynomial.algebraMap_eq]
      rw [Matrix.charmatrix, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [hD, hrep] at hmap
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    change (ρ g).trace = φ (D.lam 1 _)
    rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, hmap, Polynomial.coeff_map]
    simp [GDet.lam]
