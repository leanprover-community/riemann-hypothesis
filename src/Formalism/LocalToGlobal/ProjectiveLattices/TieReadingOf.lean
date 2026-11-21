import Formalism.LocalToGlobal.ProjectiveLattices.TieUpR

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates

variable {D : D7} {T : Top D}

structure RdData1 {j : ℕ} (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E)
    (fun Z => AC Z)) (Z : Comp (T.Q.Xo j) T.Q.c) (X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r) where
  Rg : Subring (AC Z)
  w_mem : ∀ i, d.w i Z ∈ Rg
  rd : Rg →+* (Frame X.Ψ D.R.r → ℂ)
  WE : AddSubgroup (WTZ D.host.E)
  wL_mem : d.wL ∈ WE
  wt : WE →+ Wt X.Ψ D.R.r

def TieRd1Props (h : LawsP T) {j : ℕ} (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) (Z : Comp (T.Q.Xo j) T.Q.c)
    (R : RdData1 d Z ((T.U j T.σ₀).X (κ Z))) : Prop :=
  (∀ G (hG : G ∈ R.WE), ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → ((T.U j T.σ₀).X (κ Z)).IsSec (R.wt ⟨G, hG⟩) (R.rd ⟨f, hf⟩)) ∧
  (∀ G, ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → (∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, R.rd ⟨f, hf⟩ x = 0) → f = 0) ∧
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), Even u.n → valC hG (wtA u) u.n F.1 Z ∈ R.Rg) ∧
  (∀ (u : WeightFamilies.Wt D j), Even u.n → wtZ (wtA u) u.n ∈ R.WE) ∧
  (∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (hF : valC hG (wtA u) u.n F.1 Z ∈ R.Rg),
    ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, R.rd ⟨_, hF⟩ x = rdR h j F (κ Z) x) ∧
  ∀ (u : WeightFamilies.Wt D j) (hu : wtZ (wtA u) u.n ∈ R.WE), R.wt ⟨_, hu⟩ = laU (T.U j T.σ₀) (wtA u) u.n (κ Z)

def TieRd2Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X)
    (Gen : Set (Frame X.Ψ D.R.r)) (pt : Frame X.Ψ D.R.r → (Om Z →+* ℂ)) : Prop :=
  Gen ⊆ X.dom ∧ X.dom ⊆ closure Gen ∧
  (∀ x ∈ Gen, pt x ∈ PT (Ω := Om Z) T.σ₀) ∧ (∀ P ∈ PT (Ω := Om Z) T.σ₀, ∃ x ∈ Gen, pt x = P) ∧
  (∀ G (hG : G ∈ R.WE), ∀ f (hf : f ∈ R.Rg), f ∈ AG Z G → ∀ x ∈ Gen,
    X.pnorm (R.wt ⟨G, hG⟩) (R.rd ⟨f, hf⟩) x = d.nrm Z G f (pt x)) ∧
  (∀ x ∈ Gen, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ D.R.r, lact γ (rmul x b) ∈ Gen ∧ pt (lact γ (rmul x b)) = pt x) ∧
  (∀ x ∈ Gen, ∀ x' ∈ Gen, pt x = pt x' → ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ D.R.r, x' = lact γ (rmul x b)) ∧
  (∀ x ∈ X.dom, ∀ P ∈ PT (Ω := Om Z) T.σ₀,
    (∀ G ∈ R.WE, ∀ f (hf : f ∈ R.Rg) g (hg : g ∈ R.Rg), f ∈ AG Z G → g ∈ AG Z G → g ≠ 0 →
      R.rd ⟨f, hf⟩ x = P (ratio (Ω := Om Z) f g) * R.rd ⟨g, hg⟩ x) → x ∈ Gen ∧ pt x = P) ∧
  ∀ G, ∀ f (hf : f ∈ R.Rg) g (hg : g ∈ R.Rg), f ∈ AG Z G → g ∈ AG Z G → g ≠ 0 → ∀ x ∈ Gen,
    R.rd ⟨f, hf⟩ x = pt x (ratio (Ω := Om Z) f g) * R.rd ⟨g, hg⟩ x

def TieRd3Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X) : Prop :=
  (∀ a : Om Z, ∃ (G : WTZ D.host.E) (f p : AC Z), f ∈ R.Rg ∧ p ∈ R.Rg ∧ f ∈ AG Z G ∧ p ∈ AG Z G ∧ p ≠ 0 ∧
    p ∈ Algebra.adjoin T.Q.c.F (Set.range fun i => d.w i Z) ∧ a = ratio (Ω := Om Z) f p) ∧
  ∀ x ∈ X.dom, ∃ i, R.rd ⟨d.w i Z, R.w_mem i⟩ x ≠ 0

def TieRd4Props {j : ℕ}
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z))
    (Z : Comp (T.Q.Xo j) T.Q.c) {X : ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E D.R.r} (R : RdData1 d Z X)
    (Gen : Set (Frame X.Ψ D.R.r)) : Prop :=
  ∀ x ∈ Gen, ∃ (j0 : Fin (d.N + 1)) (jj : Fin (nd X) → Fin (d.N + 1)),
    R.rd ⟨d.w j0 Z, R.w_mem j0⟩ x ≠ 0 ∧
    (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      R.rd ⟨d.w (jj k) Z, R.w_mem (jj k)⟩ (cpt X x z) / R.rd ⟨d.w j0 Z, R.w_mem j0⟩ (cpt X x z) : V (nd X))) 0).det ≠ 0


end Formalism.L2.Pj
