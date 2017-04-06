from setuptools import setup, find_packages

setup(
        name='z3gi',
        version='0.1',
        description='Grammatical inference using the Z3 SMT solver',
        long_description=open('README.md').read(),
        url='https://gitlab.science.ru.nl/rick/z3gi',
        author='Rick Smetsers',
        author_email='ricksmet@gmail.com',
        licence='MIT',
        packages=find_packages(exclude=['tests*', 'docs*']),
        install_requires=['z3-solver'],
        )
