module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLineDegreeDual
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial Matrix NumberField

noncomputable section

def dualPointCoord {K : Type} [Field K] [NumberField K] {i : ℕ} {F : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] (v : Fin i → K') :
    (Σ _ : Unit, T) → K' :=
  fun p => ∑ j, algebraMap K K' ((b p.2 : Fin i → K) j) * v j

def DualCurvePoint.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (W : Ideal (MRing (dualBlocks T))),
    IsArithVar W 1 → dualIdeal b ≤ W →
      ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (v : Fin i → K'),
        v ≠ 0 ∧ W = mCoordIdeal (dualPointCoord b v)

def PointDegCPos.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K'),
    IsArithVar (mCoordIdeal y) 1 → 0 < degC (mCoordIdeal y)

def PointArInt.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (A : HermLine (fun _ : Unit => T)) (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsSectionOn (mCoordIdeal y) A s →
      (Module.finrank ℚ K' : ℝ) * arInt (mCoordIdeal y) s A (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) =
        (degC (mCoordIdeal y) : ℝ) * ∑ σ : K' →+* ℂ, logNorm A s (fun p => σ (y p))

def PointVertR.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      (Module.finrank ℚ K' : ℝ) * vertR (mCoordIdeal y) (Fin.elim0 : Fin 0 → HermLine (fun _ : Unit => T)) s =
        (degC (mCoordIdeal y) : ℝ) * (Real.log |(Algebra.norm ℚ (aeval y s) : ℝ)| +
          Real.log (genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
            (1 : Submodule (𝓞 K') K').toAddSubgroup))

def DualLineIndex.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (K' : Type) [Field K'] [NumberField K']
    [Algebra K K'] (v : Fin i → K'), v ≠ 0 →
      genIndex ((Submodule.span (𝓞 K')
          ((fun w : Fin i → K => fun j => algebraMap K K' (w j)) '' F.lattice) ⊓
          (Submodule.span K' (Set.range fun _ : Fin 1 => v)).restrictScalars (𝓞 K')).toAddSubgroup)
        (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 => v)).toAddSubgroup *
      genIndex (Submodule.span (𝓞 K') (Set.range (dualPointCoord b v))).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup = 1

end

end GroundTheory.Heights₂.Heights
