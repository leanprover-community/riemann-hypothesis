module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
public import GroundTheory.LocalFields.Examples
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
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



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace GlobalTheory.SuppIne
open GlobalTheory.LocGL GlobalTheory.SmGL
section Transport
variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
end Transport
end GlobalTheory.SuppIne
namespace GlobalTheory.SuppIne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem ine_pol_rc_eq_char_pol_loc_rec {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D}
    {rc : GlobalTheory.SerSys.Corr D} (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) (k : Fin 2) (v : D.nd.PlG k) (n : ℕ)
    (σ : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E))) (π : QRep (D.host.g k) n)
    (e : Nonempty (π ≅ pull I k v σ)) :
    D.naut.inePol (rc k v n π) (D.ntypes.tg k v) =
      (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)).charPol
        (GlobalTheory.WeilDeligne.ineIncl _ ⟨D.ntypes.tg k v, D.ntypes.tg_mem k v⟩) := by
  rw [T.inePol _ _ _ (D.ntypes.tg_mem k v), h k v n σ π e,
    GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine _ (D.ntypes.tg_mem k v)]
theorem ine_pol_rc_eq_prod_of_has_support : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc → ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Supp.GLRep (D.host.g k)) (y : List (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])), GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL ℚ_[D.host.g k])) → D.naut.inePol (rc k v π.1 π.2) (D.ntypes.tg k v) = (y.map fun x => D.naut.inePol (rc k v x.1 (Rep.of x.rep)) (D.ntypes.tg k v)).prod := by
  intro hL D T I rc hRc k v π y hy
  obtain ⟨n, ρ⟩ := π
  have hs := hy.isSmooth
  have hi := hy.isIrreducible
  change D.naut.inePol (rc k v n ρ) _ = _
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hsupp : HasSupport (GlobalTheory.LocLanglands.cls (tr I k v ρ hs hi)).rep
      ((y : Multiset _).map (trGL (I.i k v) (continuous_symm I k v))) :=
    (hasSupport_comp (I.i k v) (I.cont k v) (continuous_symm I k v) hy).of_equiv (IrrGL.equivOf _ _ _)
  rw [_root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v n _ ρ (iso_pull I k v ρ hs hi), H.supp _ _ hsupp, Multiset.map_coe, Multiset.map_coe,
    Multiset.prod_coe, List.map_map]
  congr 1
  refine List.map_congr_left fun x _ => ?_
  rw [Function.comp_apply, _root_.GlobalTheory.SuppIne.ine_pol_rc_eq_char_pol_loc_rec hRc k v x.1 _ (Rep.of x.rep)
    (iso_pull I k v (Rep.of x.rep) x.2.rep.smooth x.2.rep.irr)]
  rfl
end GlobalTheory.SuppIne
end
end
