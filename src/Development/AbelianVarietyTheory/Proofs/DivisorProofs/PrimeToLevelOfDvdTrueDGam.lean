module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks

@[expose] public section

noncomputable section

namespace GlobalTheory.DGamOnRecord

open Formalism.BasicNotions Formalism.MainNotions NumberField
open Formalism.L2.Col (Sp hStd autLat PosStar)
open Formalism.HermitianLatticesTheory (isom IsUnimodular)
open GlobalTheory.Mem.Col2 (DGam autOrd autO gamOrd gamRanks)

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']


omit [StarRing E] in
theorem card_dvd_of_minkMult {n N M : ℕ} (hM : MinkMult N M) (hN : Module.finrank ℚ E * n ≤ N)
    (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) [Finite G] : Nat.card G ∣ M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hr : Module.finrank ℚ (Sp E n × (Fin k → ℚ)) = Module.finrank ℚ E * n + k := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  let b := Module.finBasisOfFinrankEq ℚ _ hr
  let r : G →* Module.End ℚ (Sp E n × (Fin k → ℚ)) :=
    { toFun := fun g => ((g.1 : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ).prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hr : Function.Injective r := fun g h hgh =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg Prod.fst (LinearMap.congr_fun hgh (x, 0)))
  let φ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℚ E * n + k)) ℚ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := fun g h hgh =>
    hr ((LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hgh))
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM φ.range (Finite.of_equiv _ e.toEquiv)

end Transport

end GlobalTheory.DGamOnRecord

end
