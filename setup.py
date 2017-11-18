from setuptools import setup, find_packages

setup(
        name='z3gi',
        version='0.1.1',
        description='Grammatical inference using the Z3 SMT solver',
        long_description=open('README.md').read(),
        url='https://gitlab.science.ru.nl/rick/z3gi/lata',
        author='Rick Smetsers',
        author_email='ricksmet@gmail.com',
        licence='MIT',
        packages=find_packages(exclude=['tests*', 'docs*']),
        install_requires=['z3-solver'],
        classifiers=[
            'Development Status :: 3 - Alpha',
            'Environment :: Console',
            'Intended Audience :: Science/Research',
            'License :: OSI Approved :: MIT License',
            'Operating System :: OS Independent',
            'Programming Language :: Python',
            'Programming Language :: Python :: 2.7',
            'Programming Language :: Python :: 3',
            'Topic :: Scientific/Engineering :: Artificial Intelligence',
            ]
        )
