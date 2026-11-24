module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.FormRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.OElRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.NormsAndPolarizations.CjApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
open UpperTheory.V.AlgebraTools.Det

private theorem pairOfRep_cont {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (ρ : G →* Matrix (Fin n) (Fin n) A) (h : ∀ a b, AdicCont I fun g => ρ g a b) : (GDet.ofRep ρ).IsCont I := by
  intro i N
  have hl : IsLocallyConstant (fun g : G => fun a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    letI : TopologicalSpace (A ⧸ I ^ N) := ⊥
    haveI : DiscreteTopology (A ⧸ I ^ N) := ⟨rfl⟩
    rw [IsLocallyConstant.iff_continuous]
    exact continuous_pi fun a => continuous_pi fun b => (IsLocallyConstant.iff_continuous _).1 (h a b N)
  have key : (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1))) =
      (fun M : Fin n → Fin n → A ⧸ I ^ N =>
        Ideal.Quotient.mk (I ^ N) ((-1 : A) ^ i) * (Matrix.of M).charpoly.coeff (n - i)) ∘
        (fun g a b => Ideal.Quotient.mk (I ^ N) (ρ g a b)) := by
    funext g
    simp only [Function.comp_apply, GDet.lam, (repApi ρ).2.1, map_mul]
    congr 1
    rw [← Polynomial.coeff_map, ← Matrix.charpoly_map]
    rfl
  show IsLocallyConstant (fun g => Ideal.Quotient.mk (I ^ N) ((GDet.ofRep ρ).lam i (MonoidAlgebra.single g 1)))
  rw [key]
  exact hl.comp _

private theorem pairOfRep_polar {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type)
    [CommRing R] [Algebra O R] (n : ℕ) (r : F.G₀ →* GL (Fin n) R) (P : GL (Fin n) R) (h : F.IsForm O n r P) (i : ℕ)
    (y : MonoidAlgebra R F.G₀) : (GDet.ofRep (mat r)).lam i (F.star O R n y) = (GDet.ofRep (mat r)).lam i y := by
  have key := (formRep F O R n r P h).1 R y
  have hP : (↑P : Matrix (Fin n) (Fin n) R).map ⇑(algebraMap R R) = ↑P := by
    ext a b
    simp
  rw [hP] at key
  have e : (GDet.repAlg (mat r) R) (F.star O R n y) =
      ((P⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * ((GDet.repAlg (mat r) R) y)ᵀ *
        ((P⁻¹⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    rw [inv_inv, Matrix.mul_assoc, key, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul]
  unfold GDet.lam
  rw [(repApi (mat r)).1, (repApi (mat r)).1, e, Matrix.coe_units_inv (P⁻¹), Matrix.charpoly_units_conj,
    Matrix.charpoly_transpose]

theorem UpperTheory.V.Th.Nm.pairOfRep :
    ∀ {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (r : Resid F O n) (A : Type) [CommRing A] [Algebra O A] [IsCO O A] (ρ : F.G₀ →* GL (Fin n) A) (P : GL (Fin n) A) (ψ : ∀ v, Fin n → F.Gv v →* Aˣ), 1 ≤ n → (∀ i j, AdicCont (maximalIdeal A) fun g => mat ρ g i j) → (GDet.ofRep (mat ρ)).map (res O A : A →+* ResidueField O) = r.Dbar → F.IsForm O n ρ P → (∀ v i, r.IsPsi v i (ψ v i)) → (∀ v, HasFlag (ρ.comp (F.φ v)) (ψ v)) → (∀ u, ∀ g ∈ r.Ip u, ρ g = 1) → ∃ p : Pair r A, p.D = GDet.ofRep (mat ρ) ∧ p.ψ = ψ := by
  intro l _ n F O _ _ _ r A _ _ _ ρ P ψ hn hc hred hP hψ hfl hI
  refine ⟨⟨GDet.ofRep (mat ρ), ψ, pairOfRep_cont _ _ hc, hred, hψ, fun i g => pairOfRep_polar F O A n ρ P hP i _,
    fun v g h => ?_, fun u g hg h => ?_⟩, rfl, rfl⟩
  · have h2 := oElRep F O A n ρ v _ (hfl v) g
    rw [(repApi _).2.2.1 hn, map_mul, h2, mul_zero, Matrix.trace_zero]
  · have h1 : GDet.repAlg (mat ρ) A (MonoidAlgebra.single g 1 - 1) = 0 := by
      rw [map_sub, map_one]
      simp [GDet.repAlg, mat, hI u g hg]
    rw [(repApi _).2.2.1 hn, map_mul, h1, mul_zero, Matrix.trace_zero]
