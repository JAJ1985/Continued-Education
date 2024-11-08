import pretty_errors
from pycaret.datasets import get_data
from pycaret.regression import *
from gplearn.genetic import SymbolicRegressor
from ngboost import NGBRegressor

data = get_data('insurance')
s = setup(data, target = 'charges')
print(models())

dt = create_model('dt')
print(dt)

# Train multiple_modles
multiple_models = [create_model(i) for i in ['dt', 'lr', 'xgboost']]

# Check multiple_models
type(multiple_models), len(multiple_models)
#>>>(list, 3)
print(multiple_models)

best_model = compare_models()
print(best_model)

pred_holdout = predict_model(best_model)
# Create copy of data drop target column
data2 = data.copy()
data2.drop('charges', axis=1, inplace=True)

# Generate predictions
predictions = predict_model(best_model, data = data2)

sc = SymbolicRegressor()

# Train uusing create_model
sc_trained = create_model(sc)
print(sc_trained)

ng = NGBRegressor()

# Train using create_model
ng_trained = create_model(ng)
print(ng_trained)

# Create a custom estimator

import numpy as np
from sklearn.base import BaseEstimator

class MyOwnModel(BaseEstimator):
    def __init__(self):
        self.mean = 0

    def fit(self, X, y):
        self.mean = y.mean()
        return self

    def predict(self, X):
        return np.array(X.shape[0]*[self.mean])
    
# Import MyOwnModel Class
mom = MyOwnModel()

# Train using create_model
mom_trained = create_model(mom)
# generate predictions on data
predictions = predict_model(mom_trained, data = data)

def compute_cost(A2, Y, parameters):
    m = Y.shape[1] # Number of example

    # Compute the cross-entropy
    logprobs = np.multiply(np.log(A2), Y) + np.multiply((1 - Y), (np.log(1 - A2)))
    cost = -np.sum(logprobs) / m

    cost = float(np.squeeze(cost)) # Makes sure cost is the dimension we expect.
                                   # E.g., turn
    assert(isinstance(cost, float))

    return cost