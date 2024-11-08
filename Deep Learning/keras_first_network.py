from numpy import loadtxt
from tensorflow.python.keras.models import Sequential
from tensorflow.python.keras.layers import Dense

# Load the dataset.
dataset = loadtxt(
    r'C:\\Users\\josjohn\Data\\pima-indians-diabetes.csv', delimiter=",")

# Split into input (X) and output (y) variables
X = dataset[:, 0:8]
y = dataset[:, 8]

# define the keras model
model = Sequential()
model.add(Dense(12, input_shape=(8,), activation='relu'))
model.add(Dense(8, activation='relu'))
model.add(Dense(1, activation='sigmoid'))

# compile the keras model
model.compile(loss='binary_crossentropy',
              optimizer='adam', metrics=['accuracy'])

# fit the keras model on the dataset
model.fit(X, y, epochs=150, batch_size=10)

# evaluate the keras model
_, accuracy = model.evaluate(X, y)
print('Accuracy: %.2f' % (accuracy*100))
