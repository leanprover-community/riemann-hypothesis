module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

theorem lifts : Lifts := by
  intro k _ _ _ _
  refine ⟨fun η θ h => isSmoothChar_of_isTame h.isTame, fun θ => ?_, fun η θ θ' h h' => ?_⟩
  · obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
    obtain ⟨η, hη, -⟩ := exists_isTameLift θ hϖ 1
    exact ⟨η, hη⟩
  · have hsurj : Function.Surjective (unitRes k) :=
      IsLocalRing.surjective_units_map_of_local_ringHom _ IsLocalRing.residue_surjective inferInstance
    refine MonoidHom.ext fun t => ?_
    obtain ⟨u, rfl⟩ := hsurj t
    rw [← h u, ← h' u]

theorem suppOfType_of (L : Loc) (h1 : TypeToIw) : SuppOfType := by
  intro k _ _ _ _ _ N s d hd V _ _ π hsm hirr θ hθ
  obtain ⟨v, hv0, hv⟩ := hθ
  choose μ hμ using fun a => (lifts k).2.1 (θ a)
  have hIw := h1 k N s d hd V π θ μ hμ v hv
  obtain ⟨ψ, hψ1, -, hψ3⟩ := GlobalTheory.TameIwahori.exists_prinSeries L.bz L.dzj
    (GlobalTheory.SplitRead.Irr.mk V π hsm hirr) (fun i => (lifts k).1 _ _ (hμ _)) hv0 hIw
  have hψ : ∀ i, IsTameLift (ψ i) (θ (blockOf d hd i)) := by
    intro i u
    rw [hψ1 i _ (valuation_eq_one_iff.mpr ⟨u, rfl⟩)]
    exact hμ _ u
  exact ⟨ψ, hψ, GlobalTheory.TameIwahori.isCuspSupport_of_prinSeries (GlobalTheory.SplitRead.Irr.mk V π hsm hirr)
    (fun i => (lifts k).1 _ _ (hψ i)) hψ3⟩

theorem topB_of (h1 : JacOfType) (h2 : GrpFacts) (h3 : JacProd) : TopB := by
  intro k _ _ _ _ _ N s d hd hpos V _ _ π hsm hirr θ hinj hθ
  choose μ hμ using fun a => (lifts k).2.1 (θ a)
  have hsmooth : ∀ a, IsSmoothChar (μ a) := fun a => (lifts k).1 _ _ (hμ a)
  have hf := h2 k s θ μ hinj hμ
  let G : UpperTheory.TNZ.Grp k N :=
    { s := s, d := d, pos := hpos, hd := hd, μ := μ, smooth := hsmooth,
      dist := fun a b hab => (hf a b hab).1,
      ball := fun a a' b' b h1 h2 h3 => by
        rw [(hf a' b' h2.ne).2, (hf a b (by intro h; subst h; omega)).2] }
  obtain ⟨y, hy0, hy⟩ := h1 k N s d (stdBlocks d hd) V π hsm hirr θ μ hμ hθ
  exact ⟨μ, fun a => ⟨hsmooth a, hμ a⟩, h3 k N G V π hsm hirr ⟨y, hy0, hy⟩⟩

end UpperTheory.Gal.TypesAndIwahori
