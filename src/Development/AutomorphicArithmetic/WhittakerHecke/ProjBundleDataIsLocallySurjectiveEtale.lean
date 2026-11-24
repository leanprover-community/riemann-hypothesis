module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
public import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataExistsSimplexOfRel
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

theorem UpperTheory.projBundleData_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (P.pS.app (op ⦋0⦌)) := by
  intro T W r d P
  apply Presheaf.isLocallySurjective_of_surjective
  intro U s
  obtain ⟨p, hp⟩ := Quotient.exists_rep (s : _root_.Quotient (P.relS (unop U)))
  obtain ⟨z, hz⟩ := UpperTheory.projBundleData_exists_simplex_of_rel P 0 (unop U) (fun _ => p) (fun _ _ => P.rel_refl _ p)
  refine ⟨z, ?_⟩
  rw [← hp]
  change Quotient.mk _ (P.sv z 0) = Quotient.mk _ p
  rw [hz]
