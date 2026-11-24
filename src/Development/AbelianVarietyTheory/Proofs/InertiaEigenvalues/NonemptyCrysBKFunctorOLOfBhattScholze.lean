module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphismStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystalStatement
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per

namespace GlobalTheory

theorem nonempty_crysBKFunctorOL_of_bhattScholze :
    GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → Nonempty (CrysBKFunctorOL a ϖ LL P) := by
  intro BS l _ a e _ _ ϖ LL _ P AI h
  refine ⟨BKFunctor.ofExists (fun T hT => GlobalTheory.T.exists_breuilKisin_module_basis_of_fCrystal BS l a e _ _ _ ϖ T ?_) fun M M' f => GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism BS l a e _ _ _ ϖ _ _ _ _ _ _ M.I M'.I M.isBK M'.isBK f⟩
  obtain ⟨E, j, H⟩ := (BS l _ _ _ (isAinf_ainfObj (ϖ.field a))).1 P AI h LL T hT
  exact ⟨E, j, H⟩

end GlobalTheory
