module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.JumpStepOf
public import Development.AbelianVarietyTheory.Definitions.Foundations.PowLtFirstRadius
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
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.BcMapFst

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain GlobalTheory.EtC GlobalTheory.Et GlobalTheory.GalV UpperTheory.Gal.G3
universe u v

theorem UpperTheory.Gal.G3.jBridgeInt :
    UpperTheory.Gal.Seam.IntMap → PositivityTheory.AutomorphicGaloisHodgeTate.G8.BridgeInt := by
  intro hInt E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hB γ x
  obtain ⟨φ, hφ, -⟩ := hInt E Ω l w A hA O Bw hB
  have h1 : Bw.j (algebraMap E Ω x) =
      ((algebraMap (CrystallineSemistableComparison.OK l Bw.Kw.1) Bw.Kw.1 (φ x) : Bw.Kw.1) : PadicAlgCl l) := by
    rw [hφ x]
    rfl
  have h2 : ‖Bw.j (algebraMap E Ω x)‖ ≤ 1 := by
    rw [h1]
    have hm : ‖(((φ x : Bw.Kw.1)) : PadicAlgCl l)‖₊ ≤ 1 := (φ x).2
    exact_mod_cast hm
  have h3 : ‖γ (Bw.j (algebraMap E Ω x))‖ = ‖Bw.j (algebraMap E Ω x)‖ :=
    (GlobalTheory.Cyc.Model.isom_gal γ).norm_map_of_map_zero (map_zero _) _
  rw [h3]
  exact h2
