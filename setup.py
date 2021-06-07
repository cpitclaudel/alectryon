from setuptools import setup
import alectryon

DESCRIPTION = "A library to process Coq snippets embedded in documents, " \
              "showing goals and messages for each Coq sentence."

with open("README.rst") as readme_file:
    LONG_DESCRIPTION = readme_file.read()

REQUIRED = [
    'pygments',
    'dominate',
    'beautifulsoup4',
    'docutils'
]

CLASSIFIERS = [
    "Development Status :: 5 - Production/Stable",
    "Intended Audience :: Science/Research",
    "License :: OSI Approved :: MIT License",
    "Operating System :: OS Independent",
    "Programming Language :: Python :: 3",
    "Topic :: Software Development :: Compilers",
    "Topic :: Text Editors :: Documentation",
    "Topic :: Text Processing :: Markup :: reStructuredText",
]

setup(
    name='alectryon',
    version=alectryon.__version__,
    classifiers=CLASSIFIERS,
    description=DESCRIPTION,
    long_description=LONG_DESCRIPTION,
    url='https://github.com/cpitclaudel/alectryon',
    long_description_content_type='text/x-rst',
    author=alectryon.__author__,
    author_email="clement.pitclaudel@live.com",
    install_requires=REQUIRED,
    entry_points={'console_scripts': 'alectryon=alectryon.cli:main'},
    packages=['alectryon'],
    python_requires='>=3.6',
    license='MIT',
)
