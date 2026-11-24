module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.RepApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ConjPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CpSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.DetExt
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.P1.redDet :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (k : Type) [Field k] [Algebra (ResidueField c'.O) k] [Algebra c'.O k] [IsScalarTower c'.O (ResidueField c'.O) k] (Q : PD T.ι (G T.F Ω) (PowerSeries k)), T.PsPair h k Q → ∀ ρ : K.V.frame.G₀ →* GL (Fin 4) (PowerSeries k), K.IsRho ρ Q →
          (W.GDet.ofRep (W.mat ρ)).map (PowerSeries.constantCoeff : PowerSeries k →+* k) = K.r.Dbar.map (algebraMap (ResidueField c'.O) k) := by
  intro Ω _ _ _ l _ c D T c' h K k _ _ _ _ Q hQ ρ hρ
  have hc : ∀ a : c'.O, PowerSeries.constantCoeff (algebraMap c'.O (PowerSeries k) a) = algebraMap c'.O k a := by
    intro a
    first
      | rfl
      | simp
  rw [W.Resid.Dbar, (AlgebraTools.Det.repApi (W.diagRep K.r.chib)).2.2.2.2.2.1 (algebraMap (ResidueField c'.O) k)]
  apply P1.detExt
  intro g
  rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.1, (AlgebraTools.Det.repApi _).2.1]
  obtain ⟨g', hg'⟩ := (phiKer K.V).1 g
  subst hg'
  have hlc : ∀ M : Matrix (Fin 4) (Fin 4) (PowerSeries k),
      (PowerSeries.constantCoeff : PowerSeries k →+* k) M.charpoly.leadingCoeff ≠ 0 := by
    intro M
    rw [(Matrix.charpoly_monic M).leadingCoeff, map_one]
    exact one_ne_zero
  rw [hρ g', (P1.cpSmul _ _).1, map_scaleRoots _ _ _ (hlc _), hQ.cp,
    (P1.cpSmul _ (0 : Matrix (Fin 4) (Fin 4) k)).2]
  change _ = ((Matrix.diagonal fun i => ((K.r.chib i (K.V.pr g') : (ResidueField c'.O)ˣ) : ResidueField c'.O)).map
    (algebraMap (ResidueField c'.O) k)).charpoly
  rw [Matrix.diagonal_map (map_zero _), Matrix.charpoly_diagonal]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [K.chib i g', hc, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply (↥c'.O) (ResidueField ↥c'.O) k, map_mul (algebraMap c'.O k)]
  rfl
