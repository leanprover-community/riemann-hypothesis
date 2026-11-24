module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam

namespace AffZphi

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  unfold mkZ pa
  rw [lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  unfold mkZ pb
  rw [lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem zob_ext {T : Over S} (f g : T ⟶ Zob A B) (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · exact (Out.powIsLimit A 4).hom_ext fun ⟨i⟩ => by simpa [pa] using ha i
  · exact (Out.powIsLimit B 4).hom_ext fun ⟨j⟩ => by simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by unfold pb; infer_instance

theorem sig_castAdd (i : Fin 4) : sig (Fin.castAdd 4 i) = .inl i := by fin_cases i <;> rfl

theorem sig_natAdd (j : Fin 4) : sig (Fin.natAdd 4 j) = .inr j := by fin_cases j <;> rfl

end AffZphi

open AffZphi

theorem isAffineHom_zphi : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) →
    IsAffineHom (GlobalTheory.ZarhinFam.zphi c.A B mu).left := by
  intro h M d S t c B _ _ Q la mu hZ _ hu
  have hB : IsAbelianScheme B := hZ.1
  have hA : IsAbelianScheme c.A := c.ab
  have hZab : IsAbelianScheme (Zob c.A B) := AbelianSchemeGerms.isAbelianScheme_tensor _ _
    (AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 3) (AbelianSchemeGerms.isAbelianScheme_powObj B hB 3)
  have h8 : IsAbelianScheme (Out.powObj c.A 8) := AbelianSchemeGerms.isAbelianScheme_powObj c.A hA 7
  have := hZab.comm
  have := hZab.smooth
  have := hZab.proper
  have := h8.proper
  have hfin : IsFinite ((𝟙 (Zob c.A B)) ^ d).left := GlobalTheory.GrpTangent.isFinite_id_pow _ hu
  have hlm : mu ≫ la = 𝟙 B ^ d := hZ.2.2.2.2.2.2.1
  let ν : Out.powObj c.A 8 ⟶ Zob c.A B :=
    mkZ c.A B (fun i => Out.powPr c.A (Fin.castAdd 4 i) ^ d) (fun j => Out.powPr c.A (Fin.natAdd 4 j) ≫ la)
  have key : zphi c.A B mu ≫ ν = (𝟙 (Zob c.A B)) ^ d := by
    refine zob_ext c.A B _ _ (fun i => ?_) (fun j => ?_)
    · rw [Category.assoc, mkZ_pa, MonObj.comp_pow, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp [zpr, sig_castAdd]
    · rw [Category.assoc, mkZ_pb, ← Category.assoc, zphi_powPr, MonObj.pow_comp, Category.id_comp]
      simp only [zpr, sig_natAdd, Sum.elim_inr, Category.assoc, hlm, MonObj.comp_pow, Category.comp_id]
  have hsep : IsSeparated ν.left := by
    have : IsSeparated (ν.left ≫ (Zob c.A B).hom) := by rw [Over.w ν]; infer_instance
    exact IsSeparated.of_comp ν.left (Zob c.A B).hom
  have : IsAffineHom ((zphi c.A B mu).left ≫ ν.left) := by
    rw [← Over.comp_left, key]; infer_instance
  exact IsAffineHom.of_comp _ ν.left

end GlobalTheory.ZarhinFam
