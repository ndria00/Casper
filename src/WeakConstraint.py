
class WeakConstraint:
    level : str
    weight : int
    terms : list
    body : str

    def __init__(self, body, weight, level, terms):
        self.body = body
        self.weight = weight
        self.level = level
        self.terms = terms

    def __str__(self) -> str:
        if len(self.terms) > 0:
            joined_terms = ",".join(self.terms)
            return f" :~{self.body}. [{self.weight}@{self.level}, {joined_terms}]"
        else:
            return f" :~{self.body}. [{self.weight}@{self.level}]"
    
    def is_level_variable(self):
        return isinstance(self.level, int)