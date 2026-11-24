module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHwOfFonOfCmpOfStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticesExistAllLayersOfBhattScholzeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriodStatement
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.HWL

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

theorem exists_hw_fon_cmp_ties : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
      (∀ (l : ℕ) [Fact l.Prime], LocTied l (L l) (A l)) →
      ∃ (H : HWOf L) (F : FonOf L A H), Nonempty (CmpOf L A H F) ∧ Nonempty (Formalism.MainNotions.LocalSituation.Ties L A H F) := by
  intro hBS L A hT
  obtain ⟨H, F, hC⟩ := GlobalTheory.T.exists_hwOf_fonOf_cmpOf' L A hT (fun l _ => GlobalTheory.T.wachLatticesExistAllLayers_of_bhattScholze hBS l (L l) (A l) (hT l))
  exact ⟨H, F, hC, ⟨⟨fun l _ => Classical.choice (GlobalTheory.T.nonempty_theta_deRhamFil_zero_concretePeriod l (L l) (A l) (hT l))⟩⟩⟩

end GlobalTheory.HWL
