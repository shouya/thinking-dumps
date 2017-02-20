from matplotlib.pyplot import imshow
import numpy


def cifar10(batch = '1'):
   if batch == 'meta':
       return unpickle('data/cifar/batches.meta')

   name = 'data/cifar/data_batch_%s' % batch
   if batch == 'test':
       name = 'data/cifar/test_batch'
   data = unpickle(name)

   data[b'data'] = data[b'data'].reshape(-1, 3, 32, 32)\
                                .transpose(0, 2, 3, 1)\
                                .reshape(-1, 32*32*3)\
                                .astype('float') / 255
   data[b'labels'] = numpy.array(data[b'labels'])

   return data
       

def unpickle(f):
    import pickle
    with open(f, 'rb') as fo:
        return pickle.load(fo, encoding="bytes")

