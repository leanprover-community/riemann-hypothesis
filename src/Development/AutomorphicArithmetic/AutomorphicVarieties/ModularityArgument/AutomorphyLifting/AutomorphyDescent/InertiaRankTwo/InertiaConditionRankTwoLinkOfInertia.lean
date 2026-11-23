module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.Across2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.PtLawsOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.DownCsdK

@[expose] public section

open UpperTheory.V.Z.Win.Dn

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.U3 UpperTheory.V.Base in
theorem UpperTheory.V.Z.Win.Dn.inertiaConditionRankTwoLink_of_inertia :
    UpperTheory.V.Keep.IneOf → Ine2 := by
  intro hI Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M _ L _ _ _ _ _ Φ C₀ k _ A _ _ r hr _ _ K _ _ _ _ _ _ hop W hW
  have hd : IsOpen ((Chr.dirG ℚ Ω ψ).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (H₁ := (Chr.cls ℚ Ω N).ker) (fun s hs => by
      rw [MonoidHom.mem_ker, Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hs, map_one])
      (Chr.clsFacts ℚ Ω N).1
  refine hI Ω l 2 W (η.ker ⊓ (Chr.dirG ℚ Ω ψ).ker) (hop.inter hd)
    (le_inf (Abelianization.commutator_subset_ker η) (Abelianization.commutator_subset_ker _)) ?_
  intro A' hA' g hg hH
  have hc : cycZ ℚ Ω l g = 1 := MonoidHom.mem_ker.1 ((places ℚ Ω l A').2.2.2 hA' hg)
  have hχ : chiO ℚ Ω l c.O g = 1 := by
    show Units.map _ (cycZ ℚ Ω l g) = 1
    rw [hc, map_one]
  have hP : Chr.Psi l e (Chr.dirG ℚ Ω ψ) g = 1 := by
    rw [Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, hχ, one_pow, one_mul]
    exact hH.2
  have hr1 : r g = 1 := hr.away A' hA' g hg hH.1 hP
  apply Units.ext
  rw [hW g hH.1]
  have hp : UnitaryThreeInertia.push A.val r g = 1 := by
    rw [MonoidHom.comp_apply, hr1, map_one]
  rw [hp]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [corner, GG.mat, Matrix.one_apply]
