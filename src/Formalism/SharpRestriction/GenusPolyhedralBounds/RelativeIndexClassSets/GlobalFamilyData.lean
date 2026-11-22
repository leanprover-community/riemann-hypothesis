module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit

@[expose] public section

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def etWt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  wscalar D j (g0 D * i) (by unfold g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

def a0 (D : D7) (j T : ℕ) : ℕ := T - WeightFamilies.dimY D j

structure GlobalFamilyData (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) where
  N : ℕ
  w : Fin N → B.Cusp j wL
  del : ℕ
  th' : Fin del → B.Cusp j wF
  rz : ℕ
  alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ
  th0 : Fin rz → B.Cusp j (X.wF0 wL wF)
  zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka
  rq : ℕ
  th : Fin rq → B.Mlat j ka
  iet : ℕ
  et : B.Cusp j (etWt D j iet)

  mx : (B.KO →+* ℂ) → ℝ

namespace GlobalFamilyData

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF)

end GlobalFamilyData

def PolyDom (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

end Formalism.MainNotions.Gaps.EtaleWeightGaps
