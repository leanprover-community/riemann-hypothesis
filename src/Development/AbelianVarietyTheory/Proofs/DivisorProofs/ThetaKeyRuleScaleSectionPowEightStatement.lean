module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleScaleSectionPowEight
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.thetaKeyRule_scale_section_pow_eight : ∀ κ : Rule, Homog (fun _ => 1) κ → ∀ (C : Type) [Field C] [CharZero C] (x : KeyIn C) (a : C), a ≠ 0 → ∃ (th' : x.P.L.Sec) (h' : _), a ^ 8 * (κ C ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ : C) = κ C x ∧ ∀ (g : ℕ) (hg : x.P.g = g) (m : ℕ) (I : Type) (pt : I → (baseOver (Sp C) ⟶ x.P.A)) (ϑ : I → C) (J : I → Fin g → C), ThJet x hg m pt ϑ J → ThJet ⟨x.P, x.g_pos, x.rig, x.rig_gen, th', h', x.v, x.basis⟩ hg m pt (fun i => a * ϑ i) (fun i j => a * J i j) := by
  first | exact @GlobalTheory.MBLow.ScaleJet.scale_key
