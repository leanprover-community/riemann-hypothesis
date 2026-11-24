module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsUniqueSimplexPullbackOfMapEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.projBundleData_exists_simplex_of_rel :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → P.PA.obj (op U)),
        (∀ i j, P.rel U (t i) (t j)) → ∃ z : Sx P.S n U, ∀ i, P.sv z i = t i := by
  intro T W r d P n U t ht
  choose h u hu using ht
  let F : ComposableArrows (Um d Γ(U, ⊤)) n :=
    { obj := fun i => (t i).2
      map := fun {i j} _ => ⟨(P.g (t i).1 (t j).1 (h i j), u i j), hu i j⟩
      map_id := by
        intro i
        apply Subtype.ext
        apply Prod.ext
        · exact P.g_self _ _
        · show u i i = 1
          apply Um.unit_unique (t i).2
          have e := hu i i
          rw [P.g_self] at e
          rw [Units.val_one, one_smul, ← e]
          simp
      map_comp := by
        intro i j k _ _
        apply Subtype.ext
        apply Prod.ext
        · show P.g (t i).1 (t k).1 (h i k) = P.g (t j).1 (t k).1 (h j k) * P.g (t i).1 (t j).1 (h i j)
          exact (P.g_coc _ _ _ (h i j) (h j k)).symm
        · show u i k = u j k * u i j
          apply Um.unit_unique (t k).2
          rw [← hu i k, ← P.g_coc _ _ _ (h i j) (h j k), Units.val_mul, ← Matrix.mulVec_mulVec,
            hu i j, Matrix.mulVec_smul, hu j k, smul_smul, Units.val_mul, mul_comm] }
  let x : Sx (cech P.c) n U := cechPt P.c n ((t 0).1 ≫ P.c) (fun i => (t i).1) (fun i => h i 0)
  have hx : pts P.c x = fun i => (t i).1 := pts_cechPt _ _ _ _
  have key : Sx.map P.bunV x = Sx.map (PGL.pr d) F := by
    show (P.gFun (pts P.c x) (pts_eq P.c x) : ComposableArrows (SingleObj (GL (Fin d) Γ(U, ⊤))) n) =
      F ⋙ Um.toGL d Γ(U, ⊤)
    fapply CategoryTheory.Functor.ext
    · intro i
      rfl
    · intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      show P.g (pts P.c x i) (pts P.c x j) _ = P.g (t i).1 (t j).1 (h i j)
      exact P.g_congr (congrFun hx i) (congrFun hx j) _ _
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U x F key
  refine ⟨z, fun i => ?_⟩
  show (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i,
    (Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i) = t i
  rw [hz1, hz2, hx]
  rfl
