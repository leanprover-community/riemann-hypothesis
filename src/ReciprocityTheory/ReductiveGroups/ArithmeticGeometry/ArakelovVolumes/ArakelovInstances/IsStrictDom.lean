module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y MeasureTheory Topology

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

instance instTopYq (X : Data E r) : TopologicalSpace (Yq X) :=
  inferInstanceAs (TopologicalSpace (Quot (Rel X)))

instance instMeasYq (X : Data E r) : MeasurableSpace (Yq X) := borel (Yq X)

instance instBorelYq (X : Data E r) : BorelSpace (Yq X) := ⟨rfl⟩

abbrev Ent (X : Data E r) : Type := X.Ψ × {p : Fin r × Fin r // p.2 < p.1}

def nd (X : Data E r) : ℕ := Fintype.card (Ent X)

def nmat (X : Data E r) (z : V (nd X)) : Frame X.Ψ r := fun τ a b =>
  if h : b < a then z ((Fintype.equivFin (Ent X)) ⟨τ, ⟨(a, b), h⟩⟩) else if a = b then 1 else 0

def cpt (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : Frame X.Ψ r := rmul x0 (nmat X z)

def kapW (X : Data E r) : Wt X.Ψ r := fun _ a => 2 * (a : ℤ) - ((r : ℤ) - 1)

def IsStrictDom (X : Data E r) (la : Wt X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, (∀ i j : Fin r, i < j → (j : ℕ) < X.p0 → la τ j < la τ i) ∧
    (∀ i j : Fin r, X.p0 ≤ (i : ℕ) → i < j → la τ j < la τ i) ∧
    (∀ i j : Fin r, (i : ℕ) < X.p0 → X.p0 ≤ (j : ℕ) → la τ i < la τ j)

variable (X : Data E r) [T2Space (Yq X)] [SecondCountableTopology (Yq X)]

end

end ReciprocityTheory.ChartRestriction.G.AR.Inst
