"""Detect repeated declaration names newly introduced by pooling module imports."""
from collections import defaultdict

class DeclarationOwners:
    def __init__(self):
        self.first = {}
        self.repeated = defaultdict(dict)

    def add(self, name, module, private):
        existing = self.first.get(name)
        if existing is None:
            self.first[name] = module, private
        elif existing[0] != module:
            self.repeated[name][existing[0]] = existing[1]
            self.repeated[name][module] = private

    def conflicting_groups(self, imports, owner):
        groups = {m for m in owner if owner[m] != m}
        groups.update(owner[m] for m in tuple(groups))
        pooled = defaultdict(set)
        for m, deps in imports.items():
            pooled[owner[m]].update(owner[d] for d in deps if owner[d] != owner[m])

        checks = defaultdict(list)
        for name, modules in self.repeated.items():
            for m in modules.keys() & groups:
                for other, private in modules.items():
                    if not private and owner[m] != owner[other]:
                        checks[m].append((other, name))

        def visible(graph, module, targets):
            reached, todo = set(), [module]
            while todo:
                m = todo.pop()
                if m not in reached:
                    reached.add(m)
                    todo.extend(graph[m])
            return reached & targets

        conflicts = defaultdict(set)
        for m, possible in checks.items():
            after = visible(pooled, owner[m], {owner[d] for d, _ in possible})
            if after:
                before = visible(imports, m, {d for d, _ in possible})
                for other, name in possible:
                    if owner[other] in after and other not in before:
                        conflicts[owner[m]].add((m, other, name))
        return conflicts
