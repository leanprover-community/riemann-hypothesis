module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
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

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

private theorem exists_local_lift {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {U : Scheme.{0}}
    (p : P.PA.obj (op U)) (x : U) :
    ∃ O : U.Opens, x ∈ O ∧ ∃ t : Sx (cech P.e) 0 (O : Scheme.{0}),
      ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0})) t =
        Quotient.mk (P.relS (O : Scheme.{0})) (P.PA.map O.ι.op p) := by
  obtain ⟨O, a, h, u, hx, hv⟩ := P.onto p.1 p.2 x
  refine ⟨O, hx, cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl), ?_⟩
  have key : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0}))
      (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl)) =
      Quotient.mk (P.relS (O : Scheme.{0})) (a ≫ P.ρ, P.v a) := by
    change Quotient.mk _ (P.sv (Sx.map P.bunF (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl))) 0) = _
    rw [P.sv_bunF, pts_cechPt]
  rw [key]
  exact Quotient.sound ⟨h, u, hv⟩

theorem UpperTheory.projBundleData_bundle_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} ((P.bunF ≫ P.pS).app (op ⦋0⦌)) := by
  intro T W r d P
  constructor
  intro U s
  obtain ⟨p, rfl⟩ := Quotient.exists_rep s
  choose O hO t ht using fun x => exists_local_lift P p x
  have hc : TopologicalSpace.IsOpenCover O := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hO x⟩
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hc))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact ⟨t x, ht x⟩
